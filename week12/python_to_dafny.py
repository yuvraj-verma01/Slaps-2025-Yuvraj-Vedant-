from __future__ import annotations

import argparse
import ast
import pathlib
import re
from contextlib import contextmanager
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple, Set


"""
Week 12 utility: translate a small, loop-friendly subset of Python into Dafny
so later tooling (e.g., auto_verify) can use the generated .dfy skeleton.

The translation intentionally keeps things simple:
- defaults to int types when information is missing
- emits loop blocks with placeholder invariants and optional `decreases *`
- focuses on assignments, if/while/for-range control flow, and returns
"""


INDENT = "  "

PY_TYPE_MAP = {
    "int": "int",
    "bool": "bool",
    "float": "real",
    "double": "real",
    "str": "string",
}


@dataclass
class TranslationOptions:
    module_name: str = "PythonModule"
    default_type: str = "int"
    include_invariant_placeholders: bool = True
    add_decreases_star: bool = True


class DafnyEmitter:
    def __init__(self):
        self.lines: List[str] = []
        self.level = 0

    def emit(self, text: str = "") -> None:
        if text:
            self.lines.append(f"{INDENT * self.level}{text}")
        else:
            self.lines.append("")

    @contextmanager
    def indent(self):
        self.level += 1
        try:
            yield
        finally:
            self.level -= 1

    def render(self) -> str:
        return "\n".join(self.lines)


def sanitize_module_name(name: str) -> str:
    cleaned = re.sub(r"[^A-Za-z0-9_]", "_", name).strip("_")
    if not cleaned:
        cleaned = "PythonModule"
    if cleaned[0].isdigit():
        cleaned = f"_{cleaned}"
    return cleaned


def get_name(node: ast.AST) -> str:
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        base = get_name(node.value)
        return f"{base}.{node.attr}" if base else node.attr
    return ""


def annotation_to_dafny(annotation: Optional[ast.AST], default: str) -> str:
    if annotation is None:
        return default
    if isinstance(annotation, ast.Name):
        return PY_TYPE_MAP.get(annotation.id, default)
    if isinstance(annotation, ast.Constant) and isinstance(annotation.value, str):
        return PY_TYPE_MAP.get(annotation.value, default)
    if isinstance(annotation, ast.Subscript):
        base = get_name(annotation.value)
        if base in {"List", "list", "Sequence", "Seq"}:
            inner = annotation_to_dafny(annotation.slice, default)
            return f"seq<{inner}>"
        if base in {"Array", "array"}:
            inner = annotation_to_dafny(annotation.slice, default)
            return f"array<{inner}>"
    return default


def infer_expr_type(expr: ast.AST, ctx_var_types: Dict[str, str], default: str) -> str:
    if isinstance(expr, ast.Constant):
        val = expr.value
        if isinstance(val, bool):
            return "bool"
        if isinstance(val, int):
            return "int"
        if isinstance(val, float):
            return "real"
        return default
    if isinstance(expr, ast.Name):
        return ctx_var_types.get(expr.id, default)
    if isinstance(expr, (ast.Compare, ast.BoolOp)):
        return "bool"
    if isinstance(expr, ast.UnaryOp) and isinstance(expr.op, ast.Not):
        return "bool"
    return default


def binop_to_str(op: ast.operator) -> str:
    if isinstance(op, ast.Add):
        return "+"
    if isinstance(op, ast.Sub):
        return "-"
    if isinstance(op, ast.Mult):
        return "*"
    if isinstance(op, (ast.Div, ast.FloorDiv)):
        return "/"
    if isinstance(op, ast.Mod):
        return "%"
    if isinstance(op, ast.Pow):
        return "^"
    raise ValueError(f"unsupported binary operator: {type(op).__name__}")


def cmpop_to_str(op: ast.cmpop) -> str:
    if isinstance(op, ast.Lt):
        return "<"
    if isinstance(op, ast.LtE):
        return "<="
    if isinstance(op, ast.Gt):
        return ">"
    if isinstance(op, ast.GtE):
        return ">="
    if isinstance(op, ast.Eq):
        return "=="
    if isinstance(op, ast.NotEq):
        return "!="
    raise ValueError(f"unsupported comparison operator: {type(op).__name__}")


def constant_to_dafny(val) -> str:
    if isinstance(val, bool):
        return "true" if val else "false"
    if isinstance(val, str):
        escaped = val.replace("\\", "\\\\").replace('"', '\\"')
        return f"\"{escaped}\""
    if val is None:
        return "null"
    return str(val)


def names_in_expr(expr: Optional[ast.AST]) -> List[str]:
    if expr is None:
        return []
    names: Set[str] = set()
    for node in ast.walk(expr):
        if isinstance(node, ast.Name):
            names.add(node.id)
    return sorted(names)


def collect_assigned_names_and_mutations(stmts: List[ast.stmt]) -> Tuple[List[str], bool]:
    assigned: Set[str] = set()
    has_mutation = False

    def record_target(tgt: ast.AST) -> None:
        nonlocal has_mutation
        if isinstance(tgt, ast.Name):
            assigned.add(tgt.id)
        elif isinstance(tgt, ast.Subscript):
            has_mutation = True
            if isinstance(tgt.value, ast.Name):
                assigned.add(tgt.value.id)

    def visit(node: ast.AST) -> None:
        if isinstance(node, ast.Assign):
            for tgt in node.targets:
                record_target(tgt)
        elif isinstance(node, ast.AnnAssign):
            record_target(node.target)
        elif isinstance(node, ast.AugAssign):
            record_target(node.target)
        for child in ast.iter_child_nodes(node):
            visit(child)

    for s in stmts:
        visit(s)
    return sorted(assigned), has_mutation


@dataclass
class FunctionContext:
    declared: Set[str]
    var_types: Dict[str, str]
    loop_counter: int
    func_meta: Dict
    unsupported: Set[str]
    needs_method_dec_star: bool

    def next_loop_id(self) -> int:
        loop_id = self.loop_counter
        self.loop_counter += 1
        return loop_id


class PythonToDafnyTranslator:
    def __init__(self, options: TranslationOptions):
        self.options = options
        self.emitter = DafnyEmitter()
        self.meta: Dict[str, object] = {}

    def translate(self, tree: ast.Module) -> str:
        module_name = sanitize_module_name(self.options.module_name)
        self.meta = {"module": module_name, "functions": []}
        self.emitter.emit(f"module {module_name}")
        self.emitter.emit("{")
        with self.emitter.indent():
            for node in tree.body:
                if isinstance(node, ast.FunctionDef):
                    self.translate_function(node)
                    self.emitter.emit()
                else:
                    self.emitter.emit(
                        f"// TODO: unsupported top-level statement: {type(node).__name__}"
                    )
        self.emitter.emit("}")
        return self.emitter.render()

    def record_unsupported(self, ctx: FunctionContext, label: str) -> None:
        ctx.unsupported.add(label)

    # function and statements 

    def translate_function(self, fn: ast.FunctionDef) -> None:
        ret_name = "ret"
        param_parts: List[str] = []
        var_types: Dict[str, str] = {}
        declared = set()
        loop_list: List[Dict[str, object]] = []
        unsupported: Set[str] = set()
        param_meta: List[Dict[str, str]] = []
        method_needs_dec_star = False

        for arg in fn.args.args:
            arg_type = annotation_to_dafny(arg.annotation, self.options.default_type)
            var_types[arg.arg] = arg_type
            declared.add(arg.arg)
            param_parts.append(f"{arg.arg}: {arg_type}")
            param_meta.append({"name": arg.arg, "type_guess": arg_type})

        
        if self.options.add_decreases_star:
            for node in ast.walk(fn):
                if isinstance(node, (ast.While, ast.For)):
                    method_needs_dec_star = True
                    break

        ret_type = annotation_to_dafny(fn.returns, self.options.default_type)

        signature = f"method {fn.name}({', '.join(param_parts)}) returns ({ret_name}: {ret_type})"
        self.emitter.emit(signature)
        with self.emitter.indent():
            if method_needs_dec_star:
                self.emitter.emit("decreases *  // @method_dec_star_if_needed")
            else:
                self.emitter.emit("// @method_dec_star_if_needed")
            self.emitter.emit("// @requires_placeholder")
            self.emitter.emit("// @ensures_placeholder")
        self.emitter.emit("{")

        ctx = FunctionContext(
            declared=declared | {ret_name},
            var_types={**var_types, ret_name: ret_type},
            loop_counter=0,
            func_meta={
                "name": fn.name,
                "params": param_meta,
                "ret": {"name": ret_name, "type_guess": ret_type},
                "loops": loop_list,
                "unsupported": [],
            },
            unsupported=unsupported,
            needs_method_dec_star=method_needs_dec_star,
        )

        with self.emitter.indent():
            body = list(fn.body)
            if (
                body
                and isinstance(body[0], ast.Expr)
                and isinstance(body[0].value, ast.Constant)
                and isinstance(body[0].value.value, str)
            ):
                body = body[1:]  # drop docstring
            if not body:
                self.emitter.emit("// pass")
            for stmt in body:
                self.translate_stmt(stmt, ctx, ret_name)

        self.emitter.emit("}")
        ctx.func_meta["unsupported"] = sorted(ctx.unsupported)
        self.meta.setdefault("functions", [])
        functions_list = self.meta.get("functions")
        if isinstance(functions_list, list):
            functions_list.append(ctx.func_meta)

    def translate_block(self, stmts: List[ast.stmt], ctx: FunctionContext, ret_name: str) -> None:
        for stmt in stmts:
            self.translate_stmt(stmt, ctx, ret_name)

    def translate_stmt(self, stmt: ast.stmt, ctx: FunctionContext, ret_name: str) -> None:
        if isinstance(stmt, ast.AnnAssign):
            self.translate_annassign(stmt, ctx)
        elif isinstance(stmt, ast.Assign):
            self.translate_assign(stmt, ctx)
        elif isinstance(stmt, ast.AugAssign):
            self.translate_augassign(stmt, ctx)
        elif isinstance(stmt, ast.If):
            self.translate_if(stmt, ctx, ret_name)
        elif isinstance(stmt, ast.While):
            self.translate_while(stmt, ctx, ret_name)
        elif isinstance(stmt, ast.For):
            self.translate_for(stmt, ctx, ret_name)
        elif isinstance(stmt, ast.Return):
            self.translate_return(stmt, ctx, ret_name)
        elif isinstance(stmt, ast.Expr):
            expr_text = self.safe_expr(stmt.value, ctx)
            self.emitter.emit(f"{expr_text};")
        elif isinstance(stmt, ast.Pass):
            self.emitter.emit("// pass")
        elif isinstance(stmt, (ast.Break, ast.Continue)):
            self.record_unsupported(ctx, type(stmt).__name__)
            self.emitter.emit(f"// TODO: loop control {type(stmt).__name__.lower()} not translated")
        else:
            self.record_unsupported(ctx, type(stmt).__name__)
            self.emitter.emit(f"// TODO: unsupported statement: {ast.dump(stmt, include_attributes=False)}")

    def translate_annassign(self, stmt: ast.AnnAssign, ctx: FunctionContext) -> None:
        if not isinstance(stmt.target, ast.Name):
            self.record_unsupported(ctx, type(stmt.target).__name__)
            self.emitter.emit(f"// TODO: unsupported annotated assignment target: {ast.dump(stmt.target, include_attributes=False)}")
            return
        name = stmt.target.id
        var_type = annotation_to_dafny(stmt.annotation, self.options.default_type)
        ctx.var_types.setdefault(name, var_type)
        expr_str = self.safe_expr(stmt.value, ctx) if stmt.value is not None else None

        if name not in ctx.declared:
            ctx.declared.add(name)
            if expr_str is not None:
                self.emitter.emit(f"var {name}: {var_type} := {expr_str};")
            else:
                self.emitter.emit(f"var {name}: {var_type};")
        else:
            if expr_str is not None:
                self.emitter.emit(f"{name} := {expr_str};")
            else:
                self.emitter.emit(f"// TODO: repeated annotated declaration for {name} skipped")

    def translate_assign(self, stmt: ast.Assign, ctx: FunctionContext) -> None:
        if len(stmt.targets) != 1:
            self.record_unsupported(ctx, "MultiAssign")
            self.emitter.emit(f"// TODO: multi-target assignment not supported: {ast.dump(stmt, include_attributes=False)}")
            return
        target = stmt.targets[0]
        expr_str = self.safe_expr(stmt.value, ctx)

        if isinstance(target, ast.Name):
            name = target.id
            guessed_type = infer_expr_type(stmt.value, ctx.var_types, self.options.default_type)
            ctx.var_types.setdefault(name, guessed_type)
            if name not in ctx.declared:
                ctx.declared.add(name)
                self.emitter.emit(f"var {name}: {ctx.var_types[name]} := {expr_str};")
            else:
                self.emitter.emit(f"{name} := {expr_str};")
        elif isinstance(target, ast.Subscript):
            lhs = self.safe_expr(target, ctx)
            self.emitter.emit(f"{lhs} := {expr_str};")
        else:
            self.record_unsupported(ctx, type(target).__name__)
            self.emitter.emit(f"// TODO: unsupported assignment target: {ast.dump(target, include_attributes=False)}")

    def translate_augassign(self, stmt: ast.AugAssign, ctx: FunctionContext) -> None:
        if isinstance(stmt.target, ast.Name):
            name = stmt.target.id
            expr_str = self.safe_expr(stmt.value, ctx)
            op = binop_to_str(stmt.op)
            if name not in ctx.declared:
                ctx.declared.add(name)
                ctx.var_types.setdefault(name, infer_expr_type(stmt.value, ctx.var_types, self.options.default_type))
                self.emitter.emit(f"var {name}: {ctx.var_types[name]} := {name} {op} {expr_str};")
            else:
                self.emitter.emit(f"{name} := {name} {op} {expr_str};")
        else:
            self.record_unsupported(ctx, type(stmt.target).__name__)
            self.emitter.emit(f"// TODO: unsupported augmented assignment target: {ast.dump(stmt.target, include_attributes=False)}")

    def translate_if(self, stmt: ast.If, ctx: FunctionContext, ret_name: str) -> None:
        cond = self.safe_expr(stmt.test, ctx)
        self.emitter.emit(f"if ({cond})")
        self.emitter.emit("{")
        with self.emitter.indent():
            self.translate_block(stmt.body, ctx, ret_name)
        if stmt.orelse:
            self.emitter.emit("} else {")
            with self.emitter.indent():
                self.translate_block(stmt.orelse, ctx, ret_name)
        self.emitter.emit("}")

    def translate_while(self, stmt: ast.While, ctx: FunctionContext, ret_name: str) -> None:
        cond = self.safe_expr(stmt.test, ctx)
        vars_in_scope = [{"name": n, "type_guess": t} for n, t in sorted(ctx.var_types.items())]
        loop_id = ctx.next_loop_id()
        self.emitter.emit(f"while ({cond})")
        self.emitter.emit(f"// @loop_id:{loop_id}")
        if self.options.include_invariant_placeholders:
            self.emitter.emit(f"invariant true // @inv_placeholder:{loop_id}")
        if self.options.add_decreases_star:
            ctx.needs_method_dec_star = True
            self.emitter.emit(f"decreases * // @dec_placeholder:{loop_id};")
        self.emitter.emit("{")
        with self.emitter.indent():
            self.translate_block(stmt.body, ctx, ret_name)
        self.emitter.emit("}")
        vars_modified, has_mutation = collect_assigned_names_and_mutations(stmt.body)
        ctx.func_meta["loops"].append(
            {
                "loop_id": loop_id,
                "kind": "while",
                "condition": cond,
                "vars_in_condition": names_in_expr(stmt.test),
                "vars_modified": vars_modified,
                "has_mutation": has_mutation,
                "vars_in_scope": vars_in_scope,
            }
        )

    def translate_for(self, stmt: ast.For, ctx: FunctionContext, ret_name: str) -> None:
        if not isinstance(stmt.target, ast.Name):
            self.record_unsupported(ctx, type(stmt.target).__name__)
            self.emitter.emit(f"// TODO: unsupported for-loop target: {ast.dump(stmt.target, include_attributes=False)}")
            return
        range_info = self.parse_range(stmt.iter, ctx)
        if range_info is None:
            self.record_unsupported(ctx, type(stmt.iter).__name__)
            self.emitter.emit(f"// TODO: unsupported for-loop iterable: {ast.dump(stmt.iter, include_attributes=False)}")
            return
        loop_id = ctx.next_loop_id()
        start, stop, step, comparator = range_info
        index_var = stmt.target.id
        ctx.var_types.setdefault(index_var, "int")
        vars_in_scope = [{"name": n, "type_guess": t} for n, t in sorted(ctx.var_types.items())]
        if index_var not in ctx.declared:
            ctx.declared.add(index_var)
            self.emitter.emit(f"var {index_var}: int := {start};")
        else:
            self.emitter.emit(f"{index_var} := {start};")

        loop_condition = f"{index_var} {comparator} {stop}"
        self.emitter.emit(f"while ({loop_condition})")
        self.emitter.emit(f"// @loop_id:{loop_id}")
        if self.options.include_invariant_placeholders:
            self.emitter.emit(f"invariant true // @inv_placeholder:{loop_id}")
        if self.options.add_decreases_star:
            ctx.needs_method_dec_star = True
            self.emitter.emit(f"decreases * // @dec_placeholder:{loop_id};")
        self.emitter.emit("{")
        with self.emitter.indent():
            self.translate_block(stmt.body, ctx, ret_name)
            self.emitter.emit(f"{index_var} := {index_var} + ({step});")
        self.emitter.emit("}")
        cond_names = set(names_in_expr(stmt.iter))
        cond_names.discard("range")
        cond_names.add(index_var)
        vars_modified, has_mutation = collect_assigned_names_and_mutations(
            stmt.body + [ast.parse(f"{index_var}=0").body[0]]
        )
        ctx.func_meta["loops"].append(
            {
                "loop_id": loop_id,
                "kind": "for",
                "condition": loop_condition,
                "vars_in_condition": sorted(cond_names),
                "vars_modified": vars_modified,
                "has_mutation": has_mutation,
                "vars_in_scope": vars_in_scope,
            }
        )

    def translate_return(self, stmt: ast.Return, ctx: FunctionContext, ret_name: str) -> None:
        if stmt.value is not None:
            expr_str = self.safe_expr(stmt.value, ctx)
            self.emitter.emit(f"{ret_name} := {expr_str};")
        self.emitter.emit("return;")

    # expressions

    def safe_expr(self, expr: ast.AST, ctx: FunctionContext) -> str:
        try:
            return self.expr_to_dafny(expr, ctx)
        except Exception as exc:
            self.record_unsupported(ctx, type(expr).__name__)
            self.emitter.emit(f"// TODO: expression fallback ({exc}): {ast.dump(expr, include_attributes=False)}")
            return "0"

    def expr_to_dafny(self, expr: ast.AST, ctx: FunctionContext) -> str:
        if isinstance(expr, ast.Constant):
            return constant_to_dafny(expr.value)
        if isinstance(expr, ast.Name):
            return expr.id
        if isinstance(expr, ast.BinOp):
            left = self.expr_to_dafny(expr.left, ctx)
            right = self.expr_to_dafny(expr.right, ctx)
            op = binop_to_str(expr.op)
            return f"({left} {op} {right})"
        if isinstance(expr, ast.BoolOp):
            op = "&&" if isinstance(expr.op, ast.And) else "||"
            parts = [self.expr_to_dafny(v, ctx) for v in expr.values]
            joined = f" {op} ".join(f"({p})" for p in parts) if len(parts) > 1 else parts[0]
            return joined
        if isinstance(expr, ast.UnaryOp):
            inner = self.expr_to_dafny(expr.operand, ctx)
            if isinstance(expr.op, ast.Not):
                return f"!({inner})"
            if isinstance(expr.op, ast.USub):
                return f"-({inner})"
            if isinstance(expr.op, ast.UAdd):
                return f"+({inner})"
        if isinstance(expr, ast.Compare):
            left = self.expr_to_dafny(expr.left, ctx)
            pieces = []
            current = left
            for op, comp in zip(expr.ops, expr.comparators):
                right = self.expr_to_dafny(comp, ctx)
                pieces.append(f"({current} {cmpop_to_str(op)} {right})")
                current = right
            return " && ".join(pieces) if len(pieces) > 1 else pieces[0]
        if isinstance(expr, ast.Call):
            func_name = get_name(expr.func) or self.expr_to_dafny(expr.func, ctx)
            args = [self.expr_to_dafny(a, ctx) for a in expr.args]
            return f"{func_name}({', '.join(args)})"
        if isinstance(expr, ast.Attribute):
            base = self.expr_to_dafny(expr.value, ctx)
            return f"{base}.{expr.attr}"
        if isinstance(expr, ast.Subscript):
            target = self.expr_to_dafny(expr.value, ctx)
            index = self.subscript_index(expr.slice, ctx)
            return f"{target}[{index}]"
        if isinstance(expr, ast.List):
            elts = [self.expr_to_dafny(e, ctx) for e in expr.elts]
            return f"[{', '.join(elts)}]"
        raise ValueError(f"unsupported expression: {type(expr).__name__}")

    def subscript_index(self, node: ast.AST, ctx: FunctionContext) -> str:
        if isinstance(node, ast.Slice):
            raise ValueError("slices are not supported in Dafny translation")
        return self.expr_to_dafny(node, ctx)

    def parse_range(self, node: ast.AST, ctx: FunctionContext) -> Optional[Tuple[str, str, str, str]]:
        if not isinstance(node, ast.Call):
            return None
        if get_name(node.func) != "range":
            return None
        if not (1 <= len(node.args) <= 3):
            return None

        start = "0"
        step_expr = "1"
        if len(node.args) == 1:
            stop_expr = self.safe_expr(node.args[0], ctx)
        elif len(node.args) == 2:
            start = self.safe_expr(node.args[0], ctx)
            stop_expr = self.safe_expr(node.args[1], ctx)
        else:
            start = self.safe_expr(node.args[0], ctx)
            stop_expr = self.safe_expr(node.args[1], ctx)
            step_expr = self.safe_expr(node.args[2], ctx)

        step_const = self.constant_int_value(node.args[2]) if len(node.args) == 3 else 1
        comparator = "<" if step_const is None or step_const >= 0 else ">"
        return start, stop_expr, step_expr, comparator

    @staticmethod
    def constant_int_value(node: ast.AST) -> Optional[int]:
        if isinstance(node, ast.Constant) and isinstance(node.value, int):
            return node.value
        return None


def translate_python_to_dafny_with_meta(
    src: str, options: Optional[TranslationOptions] = None
) -> Tuple[str, Dict[str, object]]:
    opts = options or TranslationOptions()
    tree = ast.parse(src)
    translator = PythonToDafnyTranslator(opts)
    translated = translator.translate(tree)
    return translated, translator.meta


def translate_python_to_dafny(src: str, options: Optional[TranslationOptions] = None) -> str:
    translated, _ = translate_python_to_dafny_with_meta(src, options)
    return translated


def main() -> None:
    ap = argparse.ArgumentParser(
        description="Translate a subset of Python into Dafny skeleton code (Week 12 helper)."
    )
    ap.add_argument("file", help="Python source file to translate.")
    ap.add_argument("--module-name", help="Dafny module name (defaults to file stem).")
    ap.add_argument(
        "--default-type",
        default="int",
        help="Fallback Dafny type to use when inference/annotations are missing (default: int).",
    )
    ap.add_argument(
        "--no-invariants",
        action="store_true",
        help="Skip inserting `invariant true` placeholders in loops.",
    )
    ap.add_argument(
        "--no-decreases-star",
        action="store_true",
        help="Skip emitting `decreases *;` after loops.",
    )
    ap.add_argument(
        "--out",
        help="Optional output path for the generated Dafny. Prints to stdout if omitted.",
    )

    args = ap.parse_args()

    src_path = pathlib.Path(args.file)
    src_text = src_path.read_text(encoding="utf-8")
    module_name = args.module_name or sanitize_module_name(src_path.stem)

    options = TranslationOptions(
        module_name=module_name,
        default_type=args.default_type,
        include_invariant_placeholders=not args.no_invariants,
        add_decreases_star=not args.no_decreases_star,
    )

    translated = translate_python_to_dafny(src_text, options)

    if args.out:
        out_path = pathlib.Path(args.out)
        out_path.write_text(translated, encoding="utf-8")
    else:
        print(translated)


if __name__ == "__main__":
    main()
