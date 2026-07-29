def sum_to(n: int) -> int:
    s = 0
    while n > 0:
        s += n
        n -= 1
    return s
