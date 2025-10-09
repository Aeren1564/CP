def read():
	s = input()
	x = 0
	sign = 0
	i = 0
	while i < len(s) and (s[i] == '+' or s[i] == '-'):
		if s[i] == '-':
			sign ^= 1
		i += 1
	while i < len(s):
		x = x << 1 | (ord(s[i]) - ord('0'))
		i += 1
	if sign:
		x = -x
	return x
def answer(x):
	if x == 0:
		print(0)
		return
	if x < 0:
		x = -x
		print('-', end = "")
	a = []
	while x:
		a.append(x & 1)
		x = x >> 1
	for i in range(len(a) - 1, -1, -1):
		print(a[i], end = "")
	print()

x = read()
y = read()

answer(x)
x += 1

x += 1
answer(x)


answer(x)
x -= 1

x -= 1
answer(x)

answer(x & y)

answer(x | y)

answer(x ^ y)

answer(x + y)

answer(x - y)

answer(x * y);

if y != 0:
	answer(x // y);

	answer(x % y);
