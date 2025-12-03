from __future__ import annotations

import json
import re
from dataclasses import dataclass, field
from typing import List, Optional, Tuple


# ============================================================
# Tokenizer
# ============================================================

@dataclass
class Token:
    kind: str
    value: str
    start: int
    end: int


KEYWORDS = {
    "method", "returns", "requires", "ensures",
    "invariant", "while", "for", "to",
    "var", "assert", "if", "else"
}

TOKEN_SPEC = [
    ("COMMENT", r"//[^\n]*"),
    ("WS",      r"[ \t\r\n]+"),
    ("OP",      r"<=|>=|==|!=|\|\||&&|:=|[+\-*/<>]"),
    ("LBRACE",  r"\{"),
    ("RBRACE",  r"\}"),
    ("LPAREN",  r"\("),
    ("RPAREN",  r"\)"),
    ("COMMA",   r","),
    ("COLON",   r":"),
    ("SEMICOL", r";"),
    ("NUMBER",  r"-?\d+"),
    ("IDENT",   r"[A-Za-z_][A-Za-z0-9_]*"),
]

MASTER_RE = re.compile(
    "|".join(f"(?P<{name}>{pattern})" for name, pattern in TOKEN_SPEC)
)


def tokenize(src: str) -> List[Token]:
    tokens: List[Token] = []
    for m in MASTER_RE.finditer(src):
        kind = m.lastgroup
        value = m.group()
        start, end = m.start(), m.end()

        if kind == "COMMENT":
            continue
        if kind == "WS":
            continue
        if kind == "IDENT" and value in KEYWORDS:
            kind = "KEYWORD"

        tokens.append(Token(kind, value, start, end))

    return tokens


# ============================================================
# AST Nodes
# ============================================================

@dataclass
class Stmt:
    pass


@dataclass
class WhileLoop(Stmt):
    condition: str
    invariants: List[str]
    body: List[Stmt]
    start: int
    end: int


@dataclass
class ForLoop(Stmt):
    var: str
    start_expr: str
    end_expr: str
    invariants: List[str]
    body: List[Stmt]
    start: int
    end: int


@dataclass
class Assign(Stmt):
    lhs: str
    rhs: str
    start: int
    end: int


@dataclass
class VarDecl(Stmt):
    name: str
    rhs: Optional[str]
    start: int
    end: int


@dataclass
class Assert(Stmt):
    expr: str
    start: int
    end: int


@dataclass
class IfStmt(Stmt):
    condition: str
    then_body: List[Stmt]
    else_body: List[Stmt]
    start: int
    end: int


@dataclass
class RawStmt(Stmt):
    text: str
    start: int
    end: int


@dataclass
class MethodDecl:
    name: str
    params: List[Tuple[str, str]]
    rets: List[Tuple[str, str]]
    requires: List[str]
    ensures: List[str]
    body: List[Stmt]
    start: int
    end: int


@dataclass
class Program:
    methods: List[MethodDecl] = field(default_factory=list)


# ============================================================
# Parser helpers
# ============================================================

class ParserError(Exception):
    pass


class Parser:
    def __init__(self, src: str, tokens: List[Token]):
        self.src = src
        self.tokens = tokens
        self.i = 0
        self.n = len(tokens)

    def peek(self) -> Optional[Token]:
        if self.i < self.n:
            return self.tokens[self.i]
        return None

    def advance(self) -> Optional[Token]:
        if self.i < self.n:
            t = self.tokens[self.i]
            self.i += 1
            return t
        return None

    def expect(self, kind: str, value: str = None) -> Token:
        t = self.peek()
        if t is None:
            raise ParserError(f"Expected {kind} but got EOF")
        if t.kind != kind:
            raise ParserError(f"Expected {kind} but got {t.kind} ({t.value})")
        if value is not None and t.value != value:
            raise ParserError(f"Expected {value} but got {t.value}")
        self.i += 1
        return t

    def match(self, kind: str, value: str = None) -> Optional[Token]:
        t = self.peek()
        if t and t.kind == kind and (value is None or t.value == value):
            self.i += 1
            return t
        return None

    # ---------------- program / methods ----------------

    def parse_program(self) -> Program:
        methods: List[MethodDecl] = []
        while self.peek() is not None:
            t = self.peek()
            if t.kind == "KEYWORD" and t.value == "method":
                methods.append(self.parse_method())
            else:
                self.advance()
        return Program(methods=methods)

    def parse_method(self) -> MethodDecl:
        kw = self.expect("KEYWORD", "method")
        name_tok = self.expect("IDENT")
        name = name_tok.value

        # Parameters
        params: List[Tuple[str, str]] = []
        if self.match("LPAREN"):
            params = self.parse_param_list()

        # Optional returns (...)
        rets: List[Tuple[str, str]] = []
        t = self.peek()
        if t and t.kind == "KEYWORD" and t.value == "returns":
            self.advance()
            self.expect("LPAREN")
            rets = self.parse_param_list()
        # requires/ensures
        requires: List[str] = []
        ensures: List[str] = []
        while True:
            t = self.peek()
            if t and t.kind == "KEYWORD" and t.value in ("requires", "ensures"):
                kw_tok = self.advance()
                expr = self.collect_spec_expr()
                if kw_tok.value == "requires":
                    requires.append(expr)
                else:
                    ensures.append(expr)
            else:
                break

        self.expect("LBRACE")
        body, end_tok = self.parse_block_contents()

        return MethodDecl(
            name=name,
            params=params,
            rets=rets,
            requires=requires,
            ensures=ensures,
            body=body,
            start=kw.start,
            end=end_tok.end,
        )

    def parse_param_list(self) -> List[Tuple[str, str]]:
        params: List[Tuple[str, str]] = []
        # empty list
        if self.match("RPAREN"):
            return params

        while True:
            # name : type
            name_tok = self.expect("IDENT")
            self.expect("COLON")
            # type is usually IDENT (like int), accept a simple IDENT
            type_tok = self.expect("IDENT")
            params.append((name_tok.value, type_tok.value))

            if self.match("COMMA"):
                continue
            else:
                self.expect("RPAREN")
                break
        return params

    def collect_spec_expr(self) -> str:
        start_tok = self.peek()
        if not start_tok:
            return ""
        start_pos = start_tok.start

        end_pos = start_pos
        j = self.i
        while j < self.n:
            t = self.tokens[j]
            if t.kind == "SEMICOL":
                end_pos = t.start
                break
            if t.kind == "KEYWORD" and t.value in {
                "requires", "ensures", "invariant",
                "method", "while", "for", "if", "else", "var", "assert"
            }:
                end_pos = t.start
                break
            if t.kind in ("LBRACE", "RBRACE"):
                end_pos = t.start
                break
            end_pos = t.end
            j += 1

        self.i = j
        return self.src[start_pos:end_pos].strip()

    # ---------------- blocks / statements ----------------

    def parse_block_contents(self) -> Tuple[List[Stmt], Token]:
        stmts: List[Stmt] = []
        depth = 1
        last_rbrace: Optional[Token] = None

        while self.peek() is not None and depth > 0:
            t = self.peek()
            if t.kind == "RBRACE":
                last_rbrace = self.advance()
                depth -= 1
                if depth == 0:
                    break
                continue

            if t.kind == "KEYWORD":
                if t.value == "while":
                    stmts.append(self.parse_while())
                    continue
                if t.value == "for":
                    stmts.append(self.parse_for())
                    continue
                if t.value == "var":
                    stmts.append(self.parse_vardecl())
                    continue
                if t.value == "assert":
                    stmts.append(self.parse_assert())
                    continue
                if t.value == "if":
                    stmts.append(self.parse_if())
                    continue

            if t.kind == "IDENT" and self._lookahead_is_assign():
                stmts.append(self.parse_assign())
                continue

            stmts.append(self.parse_rawstmt())

        if last_rbrace is None:
            raise ParserError("Unmatched '{' in block")
        return stmts, last_rbrace

    def _lookahead_is_assign(self) -> bool:
        if self.i + 1 < self.n:
            t1 = self.tokens[self.i]
            t2 = self.tokens[self.i + 1]
            return t1.kind == "IDENT" and t2.kind == "OP" and t2.value == ":="
        return False

    # ------------- specific statements -------------

    def parse_rawstmt(self) -> RawStmt:
        start_tok = self.peek()
        if not start_tok:
            raise ParserError("Unexpected EOF in raw statement")
        start = start_tok.start
        end = start_tok.end

        while self.peek() is not None:
            t = self.peek()
            if t.kind in ("SEMICOL", "LBRACE", "RBRACE"):
                if t.kind == "SEMICOL":
                    end = t.start
                    self.advance()
                break
            end = t.end
            self.advance()

        text = self.src[start:end].strip()
        return RawStmt(text=text, start=start, end=end)

    def parse_assign(self) -> Assign:
        lhs_tok = self.expect("IDENT")
        self.expect("OP", ":=")
        start = lhs_tok.start

        rhs_start_tok = self.peek()
        if not rhs_start_tok:
            return Assign(lhs=lhs_tok.value, rhs="", start=start, end=lhs_tok.end)
        rhs_start = rhs_start_tok.start
        end = rhs_start

        while self.peek() is not None:
            t = self.peek()
            if t.kind in ("SEMICOL", "LBRACE", "RBRACE"):
                if t.kind == "SEMICOL":
                    end = t.start
                    self.advance()
                break
            end = t.end
            self.advance()

        rhs = self.src[rhs_start:end].strip()
        return Assign(lhs=lhs_tok.value, rhs=rhs, start=start, end=end)

    def parse_vardecl(self) -> VarDecl:
        kw = self.expect("KEYWORD", "var")
        name_tok = self.expect("IDENT")
        start = kw.start
        rhs: Optional[str] = None

        # Optional ':' type
        if self.match("COLON"):
            if self.peek() and self.peek().kind == "IDENT":
                self.advance()

        # Optional ':=' expr
        if self.match("OP", ":="):
            rhs_start_tok = self.peek()
            if rhs_start_tok:
                rhs_start = rhs_start_tok.start
                end = rhs_start
                while self.peek() is not None:
                    t = self.peek()
                    if t.kind in ("SEMICOL", "LBRACE", "RBRACE"):
                        if t.kind == "SEMICOL":
                            end = t.start
                            self.advance()
                        break
                    end = t.end
                    self.advance()
                rhs = self.src[rhs_start:end].strip()

        self.match("SEMICOL")
        end = self.peek().start if self.peek() else name_tok.end
        return VarDecl(name=name_tok.value, rhs=rhs, start=start, end=end)

    def parse_assert(self) -> Assert:
        kw = self.expect("KEYWORD", "assert")
        start = kw.start
        expr_start_tok = self.peek()
        if not expr_start_tok:
            return Assert(expr="", start=start, end=kw.end)
        expr_start = expr_start_tok.start
        end = expr_start

        while self.peek() is not None:
            t = self.peek()
            if t.kind in ("SEMICOL", "LBRACE", "RBRACE"):
                if t.kind == "SEMICOL":
                    end = t.start
                    self.advance()
                break
            end = t.end
            self.advance()

        expr = self.src[expr_start:end].strip()
        return Assert(expr=expr, start=start, end=end)

    def parse_if(self) -> IfStmt:
        kw = self.expect("KEYWORD", "if")
        start = kw.start

        cond_start_tok = self.peek()
        if not cond_start_tok:
            raise ParserError("EOF after if")
        cond_start = cond_start_tok.start
        cond_end = cond_start

        while self.peek() is not None:
            t = self.peek()
            if t.kind == "LBRACE":
                break
            cond_end = t.end
            self.advance()
        condition = self.src[cond_start:cond_end].strip()

        self.expect("LBRACE")
        then_body, then_end = self.parse_block_contents()

        else_body: List[Stmt] = []
        t = self.peek()
        if t and t.kind == "KEYWORD" and t.value == "else":
            self.advance()
            self.expect("LBRACE")
            else_body, else_end = self.parse_block_contents()
            end = else_end.end
        else:
            end = then_end.end

        return IfStmt(
            condition=condition,
            then_body=then_body,
            else_body=else_body,
            start=start,
            end=end,
        )

    def parse_while(self) -> WhileLoop:
        kw = self.expect("KEYWORD", "while")
        start = kw.start

        cond_start_tok = self.peek()
        if not cond_start_tok:
            raise ParserError("EOF after 'while'")
        cond_start = cond_start_tok.start
        cond_end = cond_start

        # If next is LPAREN, parse (...) as condition
        if cond_start_tok.kind == "LPAREN":
            depth = 0
            first = True
            while self.peek() is not None:
                t = self.advance()
                if t.kind == "LPAREN":
                    depth += 1
                    if first:
                        cond_start = t.end
                        first = False
                elif t.kind == "RPAREN":
                    depth -= 1
                    if depth == 0:
                        cond_end = t.start
                        break
            condition = self.src[cond_start:cond_end].strip()
        else:
            # Until 'invariant' or '{'
            while self.peek() is not None:
                t = self.peek()
                if t.kind == "KEYWORD" and t.value == "invariant":
                    break
                if t.kind == "LBRACE":
                    break
                cond_end = t.end
                self.advance()
            condition = self.src[cond_start:cond_end].strip()

        # Invariants
        invariants: List[str] = []
        while True:
            t = self.peek()
            if t and t.kind == "KEYWORD" and t.value == "invariant":
                self.advance()
                inv = self.collect_spec_expr()
                if inv:
                    invariants.append(inv)
            else:
                break

        self.expect("LBRACE")
        body, end_tok = self.parse_block_contents()

        return WhileLoop(
            condition=condition,
            invariants=invariants,
            body=body,
            start=start,
            end=end_tok.end,
        )

    def parse_for(self) -> ForLoop:
        kw = self.expect("KEYWORD", "for")
        start = kw.start

        var_tok = self.expect("IDENT")
        self.expect("OP", ":=")

        # start expr until 'to'
        expr_start_tok = self.peek()
        if not expr_start_tok:
            raise ParserError("EOF in for")
        start_expr_start = expr_start_tok.start
        start_expr_end = start_expr_start
        while self.peek() is not None:
            t = self.peek()
            if t.kind == "KEYWORD" and t.value == "to":
                self.advance()
                break
            start_expr_end = t.end
            self.advance()
        start_expr = self.src[start_expr_start:start_expr_end].strip()

        # end expr until 'invariant' or '{'
        end_expr_start_tok = self.peek()
        if not end_expr_start_tok:
            raise ParserError("EOF in for")
        end_expr_start = end_expr_start_tok.start
        end_expr_end = end_expr_start
        while self.peek() is not None:
            t = self.peek()
            if t.kind == "KEYWORD" and t.value == "invariant":
                break
            if t.kind == "LBRACE":
                break
            end_expr_end = t.end
            self.advance()
        end_expr = self.src[end_expr_start:end_expr_end].strip()

        invariants: List[str] = []
        while True:
            t = self.peek()
            if t and t.kind == "KEYWORD" and t.value == "invariant":
                self.advance()
                inv = self.collect_spec_expr()
                if inv:
                    invariants.append(inv)
            else:
                break

        self.expect("LBRACE")
        body, end_tok = self.parse_block_contents()

        return ForLoop(
            var=var_tok.value,
            start_expr=start_expr,
            end_expr=end_expr,
            invariants=invariants,
            body=body,
            start=start,
            end=end_tok.end,
        )


# ============================================================
# Extraction helpers
# ============================================================

IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


def extract_identifiers(expr: str) -> List[str]:
    ids = IDENT_RE.findall(expr or "")
    bad = KEYWORDS | {"true", "false"}
    return [x for x in ids if x not in bad]


def collect_assigned_vars(stmts: List[Stmt]) -> set:
    vs = set()
    for s in stmts:
        if isinstance(s, Assign):
            vs.add(s.lhs)
        elif isinstance(s, VarDecl) and s.rhs is not None:
            vs.add(s.name)
        elif isinstance(s, WhileLoop):
            vs |= collect_assigned_vars(s.body)
        elif isinstance(s, ForLoop):
            vs |= collect_assigned_vars(s.body)
        elif isinstance(s, IfStmt):
            vs |= collect_assigned_vars(s.then_body)
            vs |= collect_assigned_vars(s.else_body)
    return vs


def collect_loops(method: MethodDecl) -> List[dict]:
    loops: List[dict] = []

    def visit_block(stmts: List[Stmt]):
        for s in stmts:
            if isinstance(s, WhileLoop):
                loops.append(loop_from_while(s))
                visit_block(s.body)
            elif isinstance(s, ForLoop):
                loops.append(loop_from_for(s))
                visit_block(s.body)
            elif isinstance(s, IfStmt):
                visit_block(s.then_body)
                visit_block(s.else_body)

    def loop_from_while(w: WhileLoop) -> dict:
        assigned = collect_assigned_vars(w.body)
        cond_vars = set(extract_identifiers(w.condition))
        # keep only vars that are actually "loop variables"
        # = assigned in body, plus those in condition that are also assigned
        loop_vars = set(assigned)
        loop_vars |= (cond_vars & assigned)
        return {
            "type": "while",
            "condition": w.condition,
            "variables": sorted(loop_vars),
            "invariants": w.invariants,
        }

    def loop_from_for(f: ForLoop) -> dict:
        assigned = collect_assigned_vars(f.body)
        loop_vars = set(assigned)
        loop_vars.add(f.var)
        return {
            "type": "for",
            "condition": f"{f.var} from {f.start_expr} to {f.end_expr}",
            "variables": sorted(loop_vars),
            "invariants": f.invariants,
        }

    visit_block(method.body)
    return loops


# ============================================================
# Public API: run_parser(path) -> summary dict
# ============================================================

def run_parser(path: str):
    """
    For this project we output a single-method summary in the form:

    {
      "method_name": "...",
      "loops": [ { type, condition, variables, invariants }, ... ],
      "preconditions": [...],
      "postconditions": [...],
      "parameters": [ {name, type}, ... ],
      "returns": [ {name, type}, ... ]
    }
    """
    with open(path, "r", encoding="utf-8") as f:
        src = f.read()

    tokens = tokenize(src)
    p = Parser(src, tokens)
    prog = p.parse_program()

    if not prog.methods:
        return {
            "method_name": None,
            "loops": [],
            "preconditions": [],
            "postconditions": [],
            "parameters": [],
            "returns": [],
        }

    # For now, follow your spec: assume one main method, take the first.
    m = prog.methods[0]

    loops = collect_loops(m)

    pre = list(m.requires)
    post = list(m.ensures)

    params = [{"name": n, "type": t} for (n, t) in m.params]
    rets = [{"name": n, "type": t} for (n, t) in m.rets]

    return {
        "method_name": m.name,
        "loops": loops,
        "preconditions": pre,
        "postconditions": post,
        "parameters": params,
        "returns": rets,
    }


# ============================================================
# CLI (for debugging)
# ============================================================

if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser(description="Dafny AST-based parser (SLAPS format)")
    ap.add_argument("file", help="Dafny file to parse")
    args = ap.parse_args()

    summary = run_parser(args.file)
    print(json.dumps(summary, indent=2))
