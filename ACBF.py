import random
import itertools
import time
import math

def geng(g): # Генерация случайной перестановки методом тасования Кнута
	for i in range(len(g)-1,0,-1):
		j = random.randint(0,i)
		k = g[j]
		g[j] = g[i]
		g[i] = k
	return g

def grev(g): # Вычисление функции обратной g
	rev = [0] * len(g)
	for i in range(len(g)):
		rev[g[i]] = i 
	return rev

def prev(p): # Вычисление перестановки обратной p
	rev = [0] * len(p)
	for i in range(len(p)):
		rev[p[i] - 1] = i + 1 
	return rev

def permutation(x,p): # Применение перестановки p к битам x
	len_p = len(p)
	res = 0
	for i in range(len_p):
		res = res |(((x >> (len_p - p[i])) & 1) << (len_p - 1 - i))
	return res

def w(x): # Вычисление веса x
	n = 0
	while x != 0:
		x = x & (x - 1)
		n += 1
	return n

def matrixD(A,B,n): # Построение матрицы D
	D = list()
	for i in range(n):
		aux = 2**n - 1
		for j in range(len(A)):
			inv = (B[j] >> (n - 1 - i)) & 1
			aux = aux & (A[j] ^ ((1-inv) * (2**n - 1)))
		D.append(aux)
	return D

def Dcheck(D): # Проверка является ли матрица D матрицей перестановки
	n = len(D)
	m = [0] * (2**n)
	for i in range(n):
		m[D[i]] += 1
	for i in range(n):
		if m[D[i]] != w(D[i]):
			return False
	return True

def permsD(D): # Извлечение всех перестановок из матрицы D
	n = len(D)
	perms = list()
	for i in range(n):
		aux = []
		for j in range(n):
			if ((D[i] >> n - 1 - j) & 1):
				aux.append(j + 1)
		if aux:
			if len(aux) == 1:
				perms.append(aux[0])
			else:
				perms.append(aux)
		else:
			return []
	s = []
	for i in range(n):
		auxv = 0
		for k in s:
			if i in k:
				auxv = 1
				break
		if auxv:
			continue
		aux = [i]
		for j in range(i+1,n):
			if perms[i] == perms[j]:
				aux.append(j)
		if len(aux) > 1:
			s.append(aux)
	newperms = [perms]
	for i in s:
		aux1 = list()
		for j in newperms:
			pperm = itertools.permutations(perms[i[0]])
			for k in pperm:
				aux2 = j.copy()
				for m in range(len(k)):
					aux2[i[m]] = k[m]
				aux1.append(aux2)
		newperms = aux1
	return newperms

def p1p2s1Test(n,texts,g): # Атака на случай {p1,p2,s1} с вычислением среднего номера строки для нарушения условия
	keys = list()
	gr = grev(g)
	pm1 = list()
	pmw = list()
	strcount = [0,0]
	for i in range(len(texts)-1):
		aux = texts[i][0] ^ texts[len(texts)-1][0]
		pm1.append(aux)
		pmw.append(w(aux))
	for i in itertools.permutations(range(1,n + 1)):
		pi2 = list(i)
		pi2r = prev(pi2)
		pm2 = list()
		sc = 0
		for j in range(len(texts)-1):
			aux = gr[permutation(texts[j][1],pi2r)] ^ gr[permutation(texts[len(texts)-1][1],pi2r)]
			if w(aux) != pmw[j]:
				sc = 1
				strcount[0] += j + 1
				strcount[1] += 1
				break
			pm2.append(aux)
		if sc:
			continue
		else:
			strcount[0] += len(texts) - 1
			strcount[1] += 1
		D = matrixD(pm1,pm2,n)
		if not Dcheck(D):
			continue
		possiblePi1 = permsD(D)
		if possiblePi1:
			for j in possiblePi1:
				sigma1 = texts[len(texts) - 1][0] ^ permutation(gr[permutation(texts[len(texts) - 1][1],pi2r)],prev(j))
				keys.append([j,pi2,sigma1])	
	return keys,strcount

def p1p2s1AvgStrTest(n:int): # Эксперимент для проверки среднего количества строк для нарушения условия
	for i in range(2,n+1):
		aux = [0,0]
		for j in range(100):
			aux[0] += p1p2s1AttackTest(i,random.randint(2,2**i),100)
			aux[1] += 1
		print(f"n={i}, avgstr={aux[0]/aux[1]}")
	return

def p1p2s1AttackWWC(g,texts:list): # Первый вариант атаки на случай {p1,p2,s1} 
	g_len = len(g)
	n = 0
	while g_len % 2 == 0 and g_len != 1:
		g_len = g_len >> 1
		n += 1
	if g_len != 1:
		print("Error:g is not boolean function!",g_len)
		return
	keys = list()
	gr = grev(g)
	pm1 = list()
	for i in range(len(texts)-1):
		aux = texts[i][0] ^ texts[len(texts)-1][0]
		pm1.append(aux)
	for i in itertools.permutations(range(1,n + 1)):
		pi2 = list(i)
		pi2r = prev(pi2)
		pm2 = list()
		for j in range(len(texts)-1):
			aux = gr[permutation(texts[j][1],pi2r)] ^ gr[permutation(texts[len(texts)-1][1],pi2r)]
			pm2.append(aux)
		D = matrixD(pm1,pm2,n)
		if not Dcheck(D):
			continue
		possiblePi1 = permsD(D)
		if possiblePi1:
			for j in possiblePi1:
				sigma1 = texts[len(texts) - 1][0] ^ permutation(gr[permutation(texts[len(texts) - 1][1],pi2r)],prev(j))
				keys.append([j,pi2,sigma1])	
	return keys

def p1p2s1Attack(g,texts:list): # Второй вариант атаки на случай {p1,p2,s1}
	g_len = len(g)
	n = 0
	while g_len % 2 == 0 and g_len != 1:
		g_len = g_len >> 1
		n += 1
	if g_len != 1:
		print("Error:g is not boolean function!",g_len)
		return
	keys = list()
	gr = grev(g)
	pm1 = list()
	pmw = list()
	for i in range(len(texts)-1):
		aux = texts[i][0] ^ texts[len(texts)-1][0]
		pm1.append(aux)
		pmw.append(w(aux))
	for i in itertools.permutations(range(1,n + 1)):
		pi2 = list(i)
		pi2r = prev(pi2)
		pm2 = list()
		sc = 0
		for j in range(len(texts)-1):
			aux = gr[permutation(texts[j][1],pi2r)] ^ gr[permutation(texts[len(texts)-1][1],pi2r)]
			if w(aux) != pmw[j]:
				sc = 1
				break
			pm2.append(aux)
		if sc:
			continue
		D = matrixD(pm1,pm2,n)
		if not Dcheck(D):
			continue
		possiblePi1 = permsD(D)
		if possiblePi1:
			for j in possiblePi1:
				sigma1 = texts[len(texts) - 1][0] ^ permutation(gr[permutation(texts[len(texts) - 1][1],pi2r)],prev(j))
				keys.append([j,pi2,sigma1])	
	return keys

def p1p2s1AttackTest(n:int,number_of_texts:int,number_of_experiments:int): # Измерение среднего количества строк до нарушения условия для случая {p1,p2,s1}
	func_size = 2**n 
	st = list()
	s = 0
	m = 0
	strcount = [0,0]
	for i in range(func_size):
		st.append(i)
	for i in range(number_of_experiments):
		g = geng(st)
		sigma1 = random.randint(0,func_size-1)
		pi1,pi2 = geng(list(range(1,n+1))),geng(list(range(1,n+1)))
		texts = set()
		while len(texts) < number_of_texts:
			x = random.randint(0,func_size-1)
			y = permutation(g[permutation(x ^ sigma1,pi1)],pi2)
			texts.add((x,y))
		texts = list(texts)
		op,sc = p1p2s1Test(n,texts,g)
		strcount[0] += sc[0]
		strcount[1] += sc[1]
		if len(op) != 1:
			m+=1
		else:
			s+=1
	avgstr = strcount[0]/strcount[1]
	print(f"Text length={n} Number of texts={number_of_texts} Experiments={number_of_experiments} p={100*s/number_of_experiments}% Key can't be uniquely determined={m}")
	return avgstr

def p1p2s1TimeTestWWC(n:int,number_of_texts:int,number_of_experiments:int):#Измерение среднего времени выполнения первого варианта атаки для случая {p1,p2,s1}
	func_size = 2**n 
	st = list()
	s = 0
	m = 0
	auxtime = [0,0]
	for i in range(func_size):
		st.append(i)
	for i in range(number_of_experiments):
		g = geng(st)
		sigma1 = random.randint(0,func_size-1)
		pi1,pi2 = geng(list(range(1,n+1))),geng(list(range(1,n+1)))
		texts = set()
		while len(texts) < number_of_texts:
			x = random.randint(0,func_size-1)
			y = permutation(g[permutation(x ^ sigma1,pi1)],pi2)
			texts.add((x,y))
		texts = list(texts)
		at1 = time.clock()
		op = p1p2s1AttackWWC(g,texts)
		at2 = time.clock()
		auxtime[0] += at2-at1
		auxtime[1] += 1
		if len(op) != 1:
			m+=1
		else:
			s+=1
	avgtime = auxtime[0]/auxtime[1]
	print(f"Text length={n} Number of texts={number_of_texts} Experiments={number_of_experiments} p={100*s/number_of_experiments}% Time={avgtime}")
	return avgtime

def p1p2s1TimeTest(n:int,number_of_texts:int,number_of_experiments:int):#Измерение среднего времени выполнения второго варианта атаки для случая {p1,p2,s1}
	func_size = 2**n 
	st = list()
	s = 0
	m = 0
	auxtime = [0,0]
	for i in range(func_size):
		st.append(i)
	for i in range(number_of_experiments):
		g = geng(st)
		sigma1 = random.randint(0,func_size-1)
		pi1,pi2 = geng(list(range(1,n+1))),geng(list(range(1,n+1)))
		texts = set()
		while len(texts) < number_of_texts:
			x = random.randint(0,func_size-1)
			y = permutation(g[permutation(x ^ sigma1,pi1)],pi2)
			texts.add((x,y))
		texts = list(texts)
		at1 = time.clock()
		op = p1p2s1Attack(g,texts)
		at2 = time.clock()
		auxtime[0] += at2-at1
		auxtime[1] += 1
		if len(op) != 1:
			m+=1
		else:
			s+=1
	avgtime = auxtime[0]/auxtime[1]
	print(f"Text length={n} Number of texts={number_of_texts} Experiments={number_of_experiments} p={100*s/number_of_experiments}% Time={avgtime}")
	return avgtime

def TimeTest1WWC(n:int,number_of_texts:int,number_of_experiments:int):# Сравнение среднего времени выполнения атак для случая {p1,p2,s1}
	func_size = 2**n 
	st = list()
	s = 0
	m = 0
	auxtime1 = [0,0]
	auxtime2 = [0,0]
	for i in range(func_size):
		st.append(i)
	for i in range(number_of_experiments):
		g = geng(st)
		sigma1 = random.randint(0,func_size-1)
		pi1,pi2 = geng(list(range(1,n+1))),geng(list(range(1,n+1)))
		texts = set()
		while len(texts) < number_of_texts:
			x = random.randint(0,func_size-1)
			y = permutation(g[permutation(x ^ sigma1,pi1)],pi2)
			texts.add((x,y))
		texts = list(texts)
		at1 = time.clock()
		op = p1p2s1AttackWWC(g,texts)
		at2 = time.clock()
		auxtime1[0] += at2-at1
		auxtime1[1] += 1
		at1 = time.clock()
		op = p1p2s1Attack(g,texts)
		at2 = time.clock()
		auxtime2[0] += at2-at1
		auxtime2[1] += 1
		if len(op) != 1:
			m+=1
		else:
			s+=1
	avgtime = [auxtime1[0]/auxtime1[1],auxtime2[0]/auxtime2[1]]
	print(f"Text length={n} Number of texts={number_of_texts} Experiments={number_of_experiments} p={100*s/number_of_experiments}% Time1={avgtime[0]} Time2={avgtime[1]}")
	return avgtime
	
def p1p2s2Test(n,texts,g): # Атака на случай {p1,p2,s2} с вычислением среднего номера строки для нарушения условия
	keys = list()
	cm2 = list()
	cm2w = list()
	strcount = [0,0]
	for i in range(len(texts)-1):
		aux = texts[i][1] ^ texts[len(texts)-1][1]
		cm2.append(aux)
		cm2w.append(w(aux))
	for i in itertools.permutations(range(1,n + 1)):
		pi1 = list(i)
		cm1 = list()
		sc = 0
		for j in range(len(texts)-1):
			aux = g[permutation(texts[j][0],pi1)] ^ g[permutation(texts[len(texts)-1][0],pi1)]
			if w(aux) != cm2w[j]:
				sc = 1
				strcount[0] += j + 1
				strcount[1] += 1
				break
			cm1.append(aux)
		if sc:
			continue
		else:
			strcount[0] += len(texts) - 1
			strcount[1] += 1
		D = matrixD(cm1,cm2,n)
		if not Dcheck(D):
			continue
		possiblePi2 = permsD(D)
		if possiblePi2:
			for j in possiblePi2:
				sigma2 = permutation(texts[len(texts) - 1][1],prev(j)) ^ g[permutation(texts[len(texts)-1][0],pi1)]
				keys.append([pi1,j,sigma2])	
	return keys,strcount

def p1p2s2AvgStrTest(n:int): # Эксперимент для проверки среднего номера строки для нарушения условия для случая {p1,p2,s2}
	for i in range(2,n+1):
		aux = [0,0]
		for j in range(100):
			aux[0] += p1p2s2AttackTest(i,random.randint(2,2**i),100)
			aux[1] += 1
		print(f"n={i}, avgstr={aux[0]/aux[1]}")
	return

def p1p2s2Attack(g,texts:list): # Второй вариант атаки на случай {p1,p2,s2}
	g_len = len(g)
	n = 0
	while g_len % 2 == 0 and g_len != 1:
		g_len = g_len >> 1
		n += 1
	if g_len != 1:
		print("Error:g is not boolean function!",g_len)
		return
	keys = list()
	cm2 = list()
	cm2w = list()
	for i in range(len(texts)-1):
		aux = texts[i][1] ^ texts[len(texts)-1][1]
		cm2.append(aux)
		cm2w.append(w(aux))
	for i in itertools.permutations(range(1,n + 1)):
		pi1 = list(i)
		cm1 = list()
		sc = 0
		for j in range(len(texts)-1):
			aux = g[permutation(texts[j][0],pi1)] ^ g[permutation(texts[len(texts)-1][0],pi1)]
			if w(aux) != cm2w[j]:
				sc = 1
				break
			cm1.append(aux)
		if sc:
			continue
		D = matrixD(cm1,cm2,n)
		if not Dcheck(D):
			continue
		possiblePi2 = permsD(D)
		if possiblePi2:
			for j in possiblePi2:
				sigma2 = permutation(texts[len(texts) - 1][1],prev(j)) ^ g[permutation(texts[len(texts)-1][0],pi1)]
				keys.append([pi1,j,sigma2])	
	return keys

def p1p2s2AttackWWC(g,texts:list): # Первый вариант атаки на случай {p1,p2,s2}
	g_len = len(g)
	n = 0
	while g_len % 2 == 0 and g_len != 1:
		g_len = g_len >> 1
		n += 1
	if g_len != 1:
		print("Error:g is not boolean function!",g_len)
		return
	keys = list()
	cm2 = list()
	for i in range(len(texts)-1):
		aux = texts[i][1] ^ texts[len(texts)-1][1]
		cm2.append(aux)
	for i in itertools.permutations(range(1,n + 1)):
		pi1 = list(i)
		cm1 = list()
		for j in range(len(texts)-1):
			aux = g[permutation(texts[j][0],pi1)] ^ g[permutation(texts[len(texts)-1][0],pi1)]
			cm1.append(aux)
		D = matrixD(cm1,cm2,n)
		if not Dcheck(D):
			continue
		possiblePi2 = permsD(D)
		if possiblePi2:
			for j in possiblePi2:
				sigma2 = permutation(texts[len(texts) - 1][1],prev(j)) ^ g[permutation(texts[len(texts)-1][0],pi1)]
				keys.append([pi1,j,sigma2])	
	return keys

def p1p2s2AttackTest(n:int,number_of_texts:int,number_of_experiments:int): # Измерение среднего количества строк до нарушения условия для случая {p1,p2,s2}
	func_size = 2**n 
	st = list()
	s = 0
	m = 0
	strcount = [0,0]
	for i in range(func_size):
		st.append(i)
	for i in range(number_of_experiments):
		g = geng(st)
		sigma2 = random.randint(0,func_size-1)
		pi1,pi2 = geng(list(range(1,n+1))),geng(list(range(1,n+1)))
		key = [pi1,pi2,sigma2]
		texts = set()
		while len(texts) < number_of_texts:
			x = random.randint(0,func_size-1)
			y = permutation(g[permutation(x,pi1)] ^ sigma2,pi2)
			texts.add((x,y))
		texts = list(texts)
		op,sc = p1p2s2Test(n,texts,g)
		strcount[0] += sc[0]
		strcount[1] += sc[1]
		if key not in op:
			print("Key:",key,'Possible Keys:',op)
		if len(op) != 1:
			m+=1
		else:
			s+=1
	avgstr = strcount[0]/strcount[1]
	print(f"Text length={n} Number of texts={number_of_texts} Experiments={number_of_experiments} p={100*s/number_of_experiments}% Key can't be uniquely determined={m}")
	return avgstr

def p1p2s2TimeTest(n:int,number_of_texts:int,number_of_experiments:int): #Измерение среднего времени выполнения второго варианта атаки для случая {p1,p2,s2}
	func_size = 2**n 
	st = list()
	s = 0
	m = 0
	auxtime = [0,0]
	for i in range(func_size):
		st.append(i)
	for i in range(number_of_experiments):
		g = geng(st)
		sigma2 = random.randint(0,func_size-1)
		pi1,pi2 = geng(list(range(1,n+1))),geng(list(range(1,n+1)))
		key = [pi1,pi2,sigma2]
		texts = set()
		while len(texts) < number_of_texts:
			x = random.randint(0,func_size-1)
			y = permutation(g[permutation(x,pi1)] ^ sigma2,pi2)
			texts.add((x,y))
		texts = list(texts)
		at1 = time.clock()
		op = p1p2s2Attack(g,texts)
		at2 = time.clock()
		auxtime[0] += at2-at1
		auxtime[1] += 1
		if key not in op:
			print("Key:",key,'Possible Keys:',op)
		if len(op) != 1:
			m+=1
		else:
			s+=1
	avgtime = auxtime[0]/auxtime[1]
	print(f"Text length={n} Number of texts={number_of_texts} Experiments={number_of_experiments} p={100*s/number_of_experiments}% Time={avgtime}")
	return avgtime

def p1p2s2TimeTestWWC(n:int,number_of_texts:int,number_of_experiments:int): #Измерение среднего времени выполнения первого варианта атаки для случая {p1,p2,s2}
	func_size = 2**n 
	st = list()
	s = 0
	m = 0
	auxtime = [0,0]
	for i in range(func_size):
		st.append(i)
	for i in range(number_of_experiments):
		g = geng(st)
		sigma2 = random.randint(0,func_size-1)
		pi1,pi2 = geng(list(range(1,n+1))),geng(list(range(1,n+1)))
		key = [pi1,pi2,sigma2]
		texts = set()
		while len(texts) < number_of_texts:
			x = random.randint(0,func_size-1)
			y = permutation(g[permutation(x,pi1)] ^ sigma2,pi2)
			texts.add((x,y))
		texts = list(texts)
		at1 = time.clock()
		op = p1p2s2AttackWWC(g,texts)
		at2 = time.clock()
		auxtime[0] += at2-at1
		auxtime[1] += 1
		if key not in op:
			print("Key:",key,'Possible Keys:',op)
		if len(op) != 1:
			m+=1
		else:
			s+=1
	avgtime = auxtime[0]/auxtime[1]
	print(f"Text length={n} Number of texts={number_of_texts} Experiments={number_of_experiments} p={100*s/number_of_experiments}% Time={avgtime}")
	return avgtime

def TimeTest2WWC(n:int,number_of_texts:int,number_of_experiments:int):# Сравнение среднего времени выполнения атак для случая {p1,p2,s2}
	func_size = 2**n 
	st = list()
	s = 0
	m = 0
	auxtime1 = [0,0]
	auxtime2 = [0,0]
	for i in range(func_size):
		st.append(i)
	for i in range(number_of_experiments):
		g = geng(st)
		sigma2 = random.randint(0,func_size-1)
		pi1,pi2 = geng(list(range(1,n+1))),geng(list(range(1,n+1)))
		texts = set()
		while len(texts) < number_of_texts:
			x = random.randint(0,func_size-1)
			y = permutation(g[permutation(x,pi1)] ^ sigma2,pi2)
			texts.add((x,y))
		texts = list(texts)
		at1 = time.clock()
		op = p1p2s2AttackWWC(g,texts)
		at2 = time.clock()
		auxtime1[0] += at2-at1
		auxtime1[1] += 1
		at1 = time.clock()
		op = p1p2s2Attack(g,texts)
		at2 = time.clock()
		auxtime2[0] += at2-at1
		auxtime2[1] += 1
		if len(op) != 1:
			m+=1
		else:
			s+=1
	avgtime = [auxtime1[0]/auxtime1[1],auxtime2[0]/auxtime2[1]]
	print(f"Text length={n} Number of texts={number_of_texts} Experiments={number_of_experiments} p={100*s/number_of_experiments}% Time1={avgtime[0]} Time2={avgtime[1]}")
	return avgtime

def p1p2exp(n,number_of_experiments):
	func_size = 2**n 
	st = list()
	for i in range(func_size):
		st.append(i)
	avgcoin = [0,0]
	for e in range(number_of_experiments):
		g = geng(st)
		pi1,pi2 = geng(list(range(1,n+1))),geng(list(range(1,n+1)))
		powers = list(1 << e for e in range(n))
		coin = [0,0]
		for k in range(n):
			xy = list()
			az = list()
			v = list(sum(bits) for bits in itertools.combinations(powers, k))
			for i in v:
				c = 0
				for j in v:
					y = permutation(g[permutation(i,pi1)],pi2)
					ga = g[j]
					if w(y) == w(ga):
						c += 1
						xy.append((i,y))
						az.append((j,ga))
				coin[0] += c
				coin[1] += 1
		avgcoin[0] += coin[0]/coin[1]
		avgcoin[1] += 1
	return avgcoin,avgcoin[0]/avgcoin[1]

def cpamatrix(n):# Создание матрицы размера m x n, все столбцы которой различны
	m = math.ceil(math.log2(n))
	t = 2**m
	P = [0] * m
	for i in range(1,m+1):
		for j in range(2**(i-1)):
			P[i-1] = (P[i-1] << int(t/(2**(i-1)))) ^ int(2**(t/(2**i))-1)
	for i in range(m):
		P[i] = P[i] >> (t - n)
	return P

def p1p2simpleattack(n,number_of_experiments):# Атака 1 с выбираемым открытым текстом для случая {p1,p2}
	func_size = 2**n 
	st = list()
	for i in range(func_size):
		st.append(i)
	cp1,cp2,cb = 0,0,0
	sc = [0,0,0,0]
	for noe in range(number_of_experiments):
		g = geng(st)
		pi1,pi2 = geng(list(range(1,n+1))),geng(list(range(1,n+1)))
		powers = list(1 << e for e in range(n))
		P,P1,C1,C = list(),list(),[g[0],g[func_size - 1]],[permutation(g[permutation(0,pi1)],pi2),permutation(g[permutation(func_size - 1,pi1)],pi2)]
		for k in range(1,3):#(1,3) for 1 and n-1
			xy = list()
			az = list()
			v = list(sum(bits) for bits in itertools.combinations(powers, (n-1)**(k-1)))
			#print(v)
			for i in v:
				c = 0
				y = permutation(g[permutation(i,pi1)],pi2)
				wy = w(y)
				xya = [i,y]
				aza = list()
				for j in v:
					ga = g[j]
					if wy == w(ga):
						c += 1
						aza.append([j,ga])
				if c > 1:
					continue
				P.append(i)
				C.append(y)
				for h in aza:
					P1.append(h[0])
					C1.append(h[1])
		sc[0] += len(P)
		sc[1] += len(P1)
		sc[2] += len(C1)
		sc[3] += len(C)
		D1 = matrixD(P,P1,n)
		D2 = matrixD(C1,C,n)
		if not Dcheck(D1):
			print("D1 trouble")
		elif not Dcheck(D2):
			print("D2 trouble")
		posp1 = permsD(D1)
		posp2 = permsD(D2)
		if len(posp1) == 1:
			cp1 += 1
			if len(posp2) == 1:
				cp2 += 1
				cb += 1
			else:
				B = cpamatrix(n)
				P2,C2,C3 = list(),list(),list()
				gr = grev(g)
				p1r = prev(posp1[0])
				for i in B:
					P2.append(permutation(gr[i],p1r))
				for i in P2:
					C2.append(g[permutation(i,posp1[0])])
					C3.append(permutation(g[permutation(i,pi1)],pi2))
				D3 = matrixD(C2,C3,n)
				p2d = permsD(D3)
				if len(p2d) == 1:
					cb += 1
		elif len(posp2) == 1:
			cp2 += 1
			gr = grev(g)
			p2r = prev(posp2[0])
			B = cpamatrix(n)
			P3 = list()
			for i in B:
				C2 = permutation(g[permutation(i,pi1)],pi2)
				P3.append(gr[permutation(C2,p2r)])
			D3 = matrixD(B,P3,n)
			p1d = permsD(D3)
			if len(p1d) == 1:
				cb += 1
	probs = [cp1/number_of_experiments,cp2/number_of_experiments,cb/number_of_experiments]
	print(f"n:{n}, number of experiments:{number_of_experiments}, p1 is uniquely defined: {probs[0]*100}%, p2 is uniquely defined: {probs[1]*100}%, p1,p2 are uniquely defined: {probs[2]*100}%")
	for i in range(len(sc)):
		sc[i] = sc[i]/number_of_experiments
	print(sc)
	return probs

def p1p2dupattack(n,number_of_experiments):# Атака 2 с выбираемым открытым текстом для случая {p1,p2}
	func_size = 2**n 
	st = list()
	for i in range(func_size):
		st.append(i)
	cp1,cp2,cb = 0,0,0
	auxs = 0
	Wkf = [0]*(n+1)
	for noe in range(number_of_experiments):
		g = geng(st)
		pi1,pi2 = geng(list(range(1,n+1))),geng(list(range(1,n+1)))
		powers = list(1 << e for e in range(n))
		P,P1,C1,C = list(),list(),[g[0],g[func_size - 1]],[permutation(g[permutation(0,pi1)],pi2),permutation(g[permutation(func_size - 1,pi1)],pi2)]
		Wk = [0]*(n+1)
		for k in range(1,2):#(1,3) for 1 and n-1
			xy = list()
			az = list()
			v = list(sum(bits) for bits in itertools.combinations(powers, (n-1)**(k-1)))
			for i in v:
				if Wk[w(g[i])] == 0:
					Wk[w(g[i])] = [[i,g[i]]]
				else:
					Wk[w(g[i])].append([i,g[i]])
			for i in v:
				c = 0
				y = permutation(g[permutation(i,pi1)],pi2)
				wy = w(y)
				aza = list()
				for j in v:
					ga = g[j]
					if wy == w(ga):
						c += 1
						aza.append([j,ga])
				P.append(i)
				C.append(y)
				pa,pz = 0,0
				if c > 1:
					pa = list()
					pz = list()
					for h in aza:
						pa.append(h[0])
						pz.append(h[1])
				else:
					pa = aza[0][0]
					pz = aza[0][1]
				P1.append(pa)
				C1.append(pz)
		for i in range(n+1):
			if Wk[i] == 0:
				continue
			Wkf[i] += len(Wk[i])
		s = []
		for i in range(len(P1)):
			auxv = 0
			for k in s:
				if i in k:
					auxv = 1
					break
			if auxv:
				continue
			aux = [i]
			for j in range(i+1,len(P1)):
				if P1[i] == P1[j]:
					aux.append(j)
			if len(aux) > 1:
				s.append(aux)
		PP1 = [P1]
		for i in s:
			aux1 = []
			for j in PP1:
				pperm = itertools.permutations(P1[i[0]])
				for k in pperm:
					aux2 = j.copy()
					for m in range(len(k)):
						aux2[i[m]] = k[m]
					aux1.append(aux2)
			PP1 = aux1
		s = []
		for i in range(len(C1)):
			auxv = 0
			for k in s:
				if i in k:
					auxv = 1
					break
			if auxv:
				continue
			aux = [i]
			for j in range(i+1,len(C1)):
				if C1[i] == C1[j]:
					aux.append(j)
			if len(aux) > 1:
				s.append(aux)
		PC1 = [C1]
		for i in s:
			aux1 = []
			for j in PC1:
				pperm = itertools.permutations(C1[i[0]])
				for k in pperm:
					aux2 = j.copy()
					for m in range(len(k)):
						aux2[i[m]] = k[m]
					aux1.append(aux2)
			PC1 = aux1
		cp1 += len(PP1)
		cp2 += len(PC1)
		keys = list()
		for i in range(len(PP1)):
			D1 = matrixD(P,PP1[i],n)
			if not Dcheck(D1):
				print("trouble 1")
				continue
			D2 = matrixD(PC1[i],C,n)
			if not Dcheck(D2):
				continue
			keys.append([permsD(D1),permsD(D2)])
		if len(keys) == 1:
			posp1 = keys[0][0]
			posp2 = keys[0][1]
			if len(posp1) == 1:
				if len(posp2) == 1:
					auxs += 1
				else:
					B = cpamatrix(n)
					P2,C2,C3 = list(),list(),list()
					gr = grev(g)
					p1r = prev(posp1[0])
					for i in B:
						P2.append(permutation(gr[i],p1r))
					for i in P2:
						C2.append(g[permutation(i,posp1[0])])
						C3.append(permutation(g[permutation(i,pi1)],pi2))
					D3 = matrixD(C2,C3,n)
					p2d = permsD(D3)
					if len(p2d) == 1:
						cb += 1
						auxs += 1
			elif len(posp2) == 1:
				gr = grev(g)
				p2r = prev(posp2[0])
				B = cpamatrix(n)
				P3 = list()
				for i in B:
					C2 = permutation(g[permutation(i,pi1)],pi2)
					P3.append(gr[permutation(C2,p2r)])
				D3 = matrixD(B,P3,n)
				p1d = permsD(D3)
				if len(p1d) == 1:
					cb += 1
					auxs += 1
	for i in range(n+1):
		Wkf[i] = Wkf[i]/number_of_experiments
	print("Wkf:",Wkf)
	print(n,auxs/number_of_experiments, cp1/number_of_experiments,cp2/number_of_experiments)
	return keys

def p1p2dupattack2(n,number_of_experiments):# Атака 2 с выбираемым открытым текстом для случая {p1,p2} с проверкой матриц перестановки перед добавлением на шаге 4
	func_size = 2**n 
	st = list()
	for i in range(func_size):
		st.append(i)
	cp1,cb = 0,0,0
	auxs = 0
	Wkf = [0]*(n+1)
	vn = [0]*n
	for noe in range(number_of_experiments):
		g = geng(st)
		pi1,pi2 = geng(list(range(1,n+1))),geng(list(range(1,n+1)))
		powers = list(1 << e for e in range(n))
		P,P1,C1,C = list(),[[]],[[g[0],g[func_size - 1]]],[permutation(g[permutation(0,pi1)],pi2),permutation(g[permutation(func_size - 1,pi1)],pi2)]
		Wk = [0]*(n+1)
		for k in range(1,2):#(1,3) for 1 and n-1
			v = list(sum(bits) for bits in itertools.combinations(powers, (n-1)**(k-1)))
			for i in v:
				if Wk[w(g[i])] == 0:
					Wk[w(g[i])] = [[i,g[i]]]
				else:
					Wk[w(g[i])].append([i,g[i]])
			auxc = -1
			for i in v:
				auxc += 1
				y = permutation(g[permutation(i,pi1)],pi2)
				P.append(i)
				C.append(y)
				wy = w(y)
				if len(Wk[wy]) > 1:
					auxlen = len(P1)
					for r in range(auxlen):
						for j in Wk[wy]:
							if j[0] in P1[0] or j[1] in C1[0]:
								continue
							auxlist1 = list()
							for e in P1[0]:
								auxlist1.append(e)
							auxlist1.append(j[0]) 
							D = matrixD(P,auxlist1,n)
							if not Dcheck(D):
								continue
							auxlist2 = list()
							for e in C1[0]:
								auxlist2.append(e)
							auxlist2.append(j[1]) 
							D = matrixD(auxlist2,C,n)
							if not Dcheck(D):
								continue
							P1.append(auxlist1)
							C1.append(auxlist2)
						P1.pop(0)
						C1.pop(0)
				else:
					auxap = Wk[wy][0]
					for j in P1:
						j.append(auxap[0])
					for j in C1:
						j.append(auxap[1])
				vn[auxc] += len(P1)
		for i in range(n+1):
			if Wk[i] == 0:
				continue
			Wkf[i] += len(Wk[i])
		cp1 += len(P1)
		keys = list()
		for i in range(len(P1)):
			D1 = matrixD(P,P1[i],n)
			if not Dcheck(D1):
				continue
			D2 = matrixD(C1[i],C,n)
			if not Dcheck(D2):
				continue
			keys.append([permsD(D1),permsD(D2)])
		if len(keys) == 1:
			posp1 = keys[0][0]
			posp2 = keys[0][1]
			if len(posp1) == 1:
				if len(posp2) == 1:
					auxs += 1
				else:
					B = cpamatrix(n)
					P2,C2,C3 = list(),list(),list()
					gr = grev(g)
					p1r = prev(posp1[0])
					for i in B:
						P2.append(permutation(gr[i],p1r))
					for i in P2:
						C2.append(g[permutation(i,posp1[0])])
						C3.append(permutation(g[permutation(i,pi1)],pi2))
					D3 = matrixD(C2,C3,n)
					p2d = permsD(D3)
					if len(p2d) == 1:
						cb += 1
						auxs += 1
			elif len(posp2) == 1:
				gr = grev(g)
				p2r = prev(posp2[0])
				B = cpamatrix(n)
				P3 = list()
				for i in B:
					C2 = permutation(g[permutation(i,pi1)],pi2)
					P3.append(gr[permutation(C2,p2r)])
				D3 = matrixD(B,P3,n)
				p1d = permsD(D3)
				if len(p1d) == 1:
					cb += 1
					auxs += 1
	for i in range(n):
		vn[i] = vn[i]/number_of_experiments
	print("vn =",vn)
	for i in range(n+1):
		Wkf[i] = Wkf[i]/number_of_experiments
	print("Wkf:",Wkf)
	print(n,auxs/number_of_experiments, cp1/number_of_experiments)
	return keys