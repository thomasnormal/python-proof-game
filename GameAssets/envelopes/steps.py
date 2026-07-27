def steps(n):
    count = 0
    while n != 0:
        if 0 < n:
            n = n - 1
        else:
            n = n + 1
        count = count + 1
    return count
