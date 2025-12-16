def sum_squares(n: int):
    i = 0
    s = 0
    while i < n:
        s = s + 2*i + 1
        i = i + 1
    return s
