import shapely
import random
from time import time
from shapely.geometry import LineString, Point


#represents every word to fill in the crossword. Later when aplying backtracking we use the value variable to assign values to every word.
class Word:
	
	#coords of the starting point
	ini_coords = ()
	
	#coords of the end point
	end_coords = ()
	
	#horizontal = 0, vertical = 1
	orientation = 0
	
	#word length
	length = 0

	#value assigned to this word
	value = ''

	def __str__(self):
		return 'Word(ini_coords:' + str(self.ini_coords) + ', end_coords:' + str(self.end_coords) + ', orientation:' + str(self.orientation) + ', length:' + str(self.length) + ', value:' + self.value + ')'

def readCrossword(filename):
	crossword = []
	with open(filename, 'r') as cfile:
		lines = cfile.readlines()
	for line in lines:
		replaced = line.replace("\t", "")
		replaced = replaced.replace("\n", "")
		replaced = replaced.replace(" ", "")
		crossword.append(list(replaced))
	return crossword

def readDictionary(filename):
	dictionary = []
	with open(filename, 'r') as dfile:
		words = dfile.readlines()
	for word in words:
		replaced = word.replace("\n", "")
		dictionary.append(replaced)
	return dictionary

#detects vertical and horizontal words in the crossword
def findCrosswordHorizontalWords(crossword):
	h_words = []
	v_words = []
	row_index = 0

	for row in range(len(crossword)):
		
		column = 0
		word = Word()
		finished = False
		anterior = '#'

		while column <= len(crossword[row])-1:
			
			if crossword[row][column] == '0':
				
				if anterior == '0':
					word.length += 1
					anterior = '0'
					if column == len(crossword[row])-1:
						if not finished:
							finished = True
						word.end_coords = (row, column)
						anterior = '#'

				elif anterior == "#":
					if finished:
						finished = False
					word.ini_coords = (row, column)
					word.length += 1
					anterior = '0'

			elif crossword[row][column] == '#':
				
				if anterior == '0':
					if not finished:
						finished = True
					if word.length > 1:
						word.end_coords = (row, column-1)
					else:
						word = Word()
					anterior = '#'

			if word.length > 1 and finished:
				word.orientation = 0
				h_words.append(word)
				word = Word()
				finished = False	

			column += 1
		
	return h_words

def findCrosswordVerticalWords(crossword):
	v_words = []
	word = Word()
	#word = [(), (), 0]
	started = False
	
	for column in range(0, len(crossword[0])):
		started = False
		for row in range(0, len(crossword)-1):
			if crossword[row][column] == '0' and crossword[row+1][column] == '0':
				if started == False:
					started = True
					word.ini_coords = (row, column)
				
				if row == len(crossword)-2 and started:
					word.end_coords = (row+1, column)
					word.length = word.end_coords[0] - word.ini_coords[0] + 1
					word.orientation = 1
					v_words.append(word)
					word = Word()
					started = False
			else:
				if started:
					word.end_coords = (row, column)
					word.length = word.end_coords[0] - word.ini_coords[0] + 1
					word.orientation = 1
					v_words.append(word)
					word = Word()
					started = False
	return v_words

def insertWord(crossword, word, coord, orientation):
	pos_count = 0
	for char in word:
		if not orientation:
			crossword[coord[0]][coord[1]+pos_count] = char
		else:
			crossword[coord[0]+pos_count][coord[1]] = char
		pos_count += 1
	return crossword

#tractarem les paraules com a linees per així trobar intersecció sense complicar-nos
def checkIntersections(w1, w2):
	line1 = LineString([w1.ini_coords, w1.end_coords])
	line2 = LineString([w2.ini_coords, w2.end_coords])

	int_point = line1.intersection(line2)

	if not int_point.is_empty:
		return [int_point.coords[0]]
	else:
		return []

#checks every assigned element with Var
def satisfyConstrains(var, LVA):
	if LVA != None:
		for word in LVA:
			#if orientation is equal they will never interesect!
			if var.orientation != word.orientation:
				intersection = checkIntersections(var, word)
				if len(intersection) != 0:
					if var.orientation == 0:
						if var.value[int(intersection[0][1]-var.ini_coords[1])] != word.value[int(intersection[0][0]-word.ini_coords[0])]:
							return False
					else:
						if var.value[int(intersection[0][0]-var.ini_coords[0])] != word.value[int(intersection[0][1]-word.ini_coords[1])]:
							return False
	return True

#returns all the possibles values from the dom for the desired variable
def getDomForVariable(var, LVA, D):
	possibles_values = []
	
	for val in D:
		if len(val) == var.length:
			possibles_values.append(val)
	
	for item in LVA:
		if item.value in possibles_values:
			possibles_values.remove(item.value)

	return possibles_values

#backtracking algorithm
def backtracking(LVA, LVNA, D):

	#theres no variables to assign a value so we finished
	if len(LVNA) == 0:
		return LVA

	var = LVNA[0]
	
	mod_dom = getDomForVariable(var, LVA, D)

	for val in mod_dom:
		#creem variable aux per fer la comprovació i així no fer assignacions que no cumpleixen restriccions a var
		aux = var
		aux.value = val
		if satisfyConstrains(aux, LVA):
			var.value = val
			res = backtracking(LVA+[var], LVNA[1:], D)
			if res != None:
				return res
			var.value = ''

	return None

#gets list of initial domains for forward checking
def getInitialDomains(LVNA, D):
	domains = []
	for element in LVNA:
		element_domain = []
		for val in D:
			if len(val) == element.length:
				element_domain.append(val)
		domains.append(element_domain)
	return domains

def updateDomains(var, LVA, LVNA, D):
	domains = []
	for i in range(0, len(LVNA)):
		new_dom = []
		dom = D[i]
		val = LVNA[i]

		for value in dom:
			val.value = value
			if satisfyConstrains(val, LVA+[var]):
				new_dom.append(value)

		domains.append(new_dom)
	return domains

def checkDomains(new_domains):
	for dom in new_domains:
		if len(dom) == 0:
			return False
	return True

def forward_checking(LVA, LVNA, D):
	#theres no variables to assign a value so we finished
	if len(LVNA) == 0:
		return LVA
	var = LVNA[0]
	mod_dom = D[0]

	for val in mod_dom:
		#creem variable aux per fer la comprovació i així no fer assignacions que no cumpleixen restriccions a var
		aux = var
		aux.value = val
		if satisfyConstrains(aux, LVA):
			var.value = val
			#update domains
			new_dom = updateDomains(var, LVA, LVNA[1:], D[1:])
			if checkDomains(new_dom):
				res = forward_checking(LVA+[var], LVNA[1:], new_dom)
			if checkDomains(new_dom) and res != None:
				return res
			var.value = ''

	return None



cw = readCrossword("crossword_CB_v2.txt")
dic = readDictionary("diccionari_CB_v2.txt")
h_w = findCrosswordHorizontalWords(cw)
v_w = findCrosswordVerticalWords(cw)
total_words = h_w + v_w
random.shuffle(total_words)
lva = []
fw_dic = getInitialDomains(total_words, dic)
t_ini = time()
result = backtracking(lva, total_words, dic)
t_final = time()-t_ini

print("---- Crossword ----")
for line in cw:
	print(line)
print("---- Dictionary ----")
print(dic)
print("---- Horizontal Words ----")
for hw in h_w:
	print(hw)
print("---- Vertical Words ----")
for wd in v_w:
	print(wd)
print("---- Backtracking Solution ----")

for va in result:
	insertWord(cw, va.value, va.ini_coords, va.orientation)

for l in cw:
	print(l)

print("---- Backtracking Time ----")
print("Execution time:", t_final, "seconds")

t_ini2 = time()
fw_result = forward_checking(lva, total_words, fw_dic)
t_final2 = time()-t_ini2

print("---- Forward Checking Solution ----")
for fwr in fw_result:
	insertWord(cw, fwr.value, fwr.ini_coords, fwr.orientation)
for s in cw:
	print(s)
print("---- Forward Checking Time ----")
print("Execution time:", t_final2, "seconds")