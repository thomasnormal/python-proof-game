def odd_sum(n):
    total = 0
    k = 0
    while k < n:
        total = total + 2 * k + 1
        k = k + 1
    return total
