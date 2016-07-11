'''
Progetto Sistemi Operativi 2014-15
Simulazione dell'allocazione della memoria tramite gli algoritmi First, Best e Worst Fit.
Studente: Iuffrida Davide
Matricola: 445987
'''

from __future__ import division
import random
import math
import sys
import copy
import datetime
import re

#Classe per definire i colori da utilizzare nei vari print sulla shell
class Colors:
	Black = '\033[0;30m'
	White = '\033[1;37m'
	Red = '\033[0;31m'
	Blue = '\033[0;34m'
	Green = '\033[0;32m'
	Yellow = '\033[0;33m'
	LightGray = '\033[0;37m'
	DarkGray = '\033[1;30m'
	BoldRed = '\033[1;31m'
	BoldBlue = '\033[1;34m'
	BoldGreen = '\033[1;32m'
	BoldYellow = '\033[1;33m'
	Default = '\033[39m'

#Classe per effettuare i print tutti assieme, senza dover scrivere i comandi piu' volte
class Log:
	def __init__(self, filename, permission):
		#Creo un file di log se non esiste. Altrimenti continuo a scrivere.
		self.log = open(filename + ".txt", permission)
		#Creo un secondo file di log in cui salvo il testo con i caratteri di escape per i colori
		self.coloredLog = open(filename + "_colored.txt", permission)

	#Stampo il testo
	def write(self, text):
		#Print su shell
		print text
		#Log del testo su file con i colori
		self.coloredLog.write(text + "\n")
		#Tramite Regex, rimuovo i colori dal testo
		text = re.sub("\\033\[.*?m", '', text)
		#Log del testo su file senza colori
		self.log.write(text + "\n")

#Classe che conterra' informazioni sui singoli processi
class Process:
	def __init__(self, processSize, memoryBlock, startTime, workingTime):
		#Dimensione del processo
		self.size = processSize
		#Blocco di Memoria in cui risiede (riferimento all'istanza)
		#Se non e' allocato, sara' di valore None
		self.block = memoryBlock
		#Tempo di entrata in esecuzione del processo
		self.startTime = startTime
		#Tempo richiesto dal processo durante l'esecuzione
		self.workingTime = workingTime

#Classe che conterra' le informazioni riguardo ai singoli blocchi di memoria
#Un blocco di memoria avra' range [start, end)
class MemoryBlock:
	def __init__(self, startValue, endValue):
		#Valore di inizio del blocco di memoria
		self.start = startValue
		#Valore di fine del blocco di memoria
		self.end = endValue
		#Dimensione totale del blocco di memoria
		self.size = endValue - startValue
		#Controllo se il blocco e' allocato
		self.isAllocated = False

	#Aggiorna la dimensione totale del blocco di memoria
	def updateSize(self):
		self.size = self.end - self.start


#Classe tramite la quale gestiremo la memoria
class Memory:
	def __init__(self, memorySize, logger):
		#Dimensione della memoria
		self.size = memorySize
		#Inizializzo un array per i blocchi di memoria
		self.memoryBlocks = []
		#Aggiungo un singolo blocco per l'intera dimensione della memoria
		self.memoryBlocks.append(MemoryBlock(0, memorySize))
		#Inizializzo un array per la freelist
		self.freeList = []
		#Aggiungo alla freeList il blocco della memoria
		self.freeList.append(self.memoryBlocks[0])
		#Inizializzo un array per i processi in esecuzione
		self.processList = []
		#Variabile per contenere l'istanza della classe Log
		self.logging = logger

	#Ci permette di dividere un blocco di memoria in due parti, aggiornando anche la freelist
	def splitMemory(self, memoryBlock, processSize):
		startFirstBlock = memoryBlock.start
		splitPoint = memoryBlock.start + processSize
		endSecondBlock = memoryBlock.end

		self.freeList.remove(memoryBlock)
		idxBlock = self.memoryBlocks.index(memoryBlock)
		self.memoryBlocks.remove(memoryBlock)

		idxNewBlock = idxBlock + 1

		leftBlock = MemoryBlock(startFirstBlock, splitPoint)
		rightBlock = MemoryBlock(splitPoint, endSecondBlock)

		self.memoryBlocks.insert(idxBlock, leftBlock)
		self.memoryBlocks.insert(idxNewBlock, rightBlock)

		self.freeList.append(rightBlock)

		return leftBlock

	#Ci permette di unire due blocchi vicini in un singolo blocco piu' grande
	def joinMemory(self):
		i = 0
		countMemoryBlocks = len(self.memoryBlocks)

		while i < countMemoryBlocks:
			j = i + 1

			if(j >= countMemoryBlocks):
				break

			if(not self.memoryBlocks[i].isAllocated and not self.memoryBlocks[j].isAllocated):

				#Update Freelist
				countFreeBlocks = len(self.freeList)
				k = 0
				while k < countFreeBlocks:
					if self.freeList[k] == self.memoryBlocks[i] or self.freeList[k] == self.memoryBlocks[j]:
						del self.freeList[k]
						countFreeBlocks -= 1
					else:
						k += 1

				endValue = self.memoryBlocks[j].end
				self.memoryBlocks.remove(self.memoryBlocks[j])
				self.memoryBlocks[i].end = endValue

				self.memoryBlocks[i].updateSize()

				self.freeList.append(self.memoryBlocks[i])

				countMemoryBlocks -= 1
				continue

			i += 1

	#Ci permette di inserire un blocco nella freelist se non lo si ha ancora
	def checkFreeList(self):
		for i in range(0, len(self.memoryBlocks)):
			if not self.memoryBlocks[i].isAllocated and not self.memoryBlocks[i] in self.freeList:
				inList = True
				for j in range(0, len(self.freeList)):
					if self.freeList[j] == self.memoryBlocks[i]:
						inList = True
					else:
						inList = False

				if not inList:
					self.freeList.append(self.memoryBlocks[i])

#Classe che esegue gli algoritmi di allocazione per i processi
class AllocationManager:
	def __init__(self, memory, processList, logger):
		#Riferimento alla memoria
		self.memory = memory
		#Lista con i processi in attesa di entrare in esecuzione
		self.waitProcessList = processList
		#Riferimento all'istanza della classe Log
		self.logging = logger

	#Eseguira' l'algoritmo First-Fit per inserire i processi in memoria
	#Verra' scelto il primo blocco abbastanza grande da contenere il processo
	def firstFit(self):
		#Inizializzo l'orologio, il contatore per i confronti,
		#il contatore di frammentazioni esterne e variabile di calcolo
		currentTimer = 0
		countComparisons = 0
		countAllocationFail = 0
		countExternalFrag = 0
		percentExtFrag = 0

		logging.write(Colors.BoldRed + "First-Fit")

		while len(self.waitProcessList) > 0:
			#Puliamo la memoria da possibili processi che hanno completato la loro esecuzione
			self.clearMemory()
			#Uniamo gli spazi di memoria vicini
			self.memory.joinMemory()
			#Controllo la freelist per blocchi di memoria non presenti
			self.memory.checkFreeList()
			#Cerco un processo che deve entrare in questo istante di tempo
			processIdx = self.checkForProcesses(currentTimer)
			#Inizio la variabile per la frammentazione esterna
			IsSmall = True

			#Proviamo l'allocazione solo se un processo deve entrare adesso
			if(processIdx != -1):
				#Recuperiamo il processo dalla lista dei processi in attesa
				waitingProcess = self.waitProcessList[processIdx]
				for i in range(0, len(self.memory.freeList)):
					#Incrementiamo il costo del confronto
					countComparisons += 1
					#Se il processo ha una dimensione minore di quella del blocco libero allora...
					if(self.memory.freeList[i].size >= waitingProcess.size):
						#Non e' troppo piccolo per contenere il processo
						IsSmall = False
						#Alloca il processo
						self.allocateProcess(i, waitingProcess)
						#Rimuove il processo dalla lista dei processi pronti
						self.waitProcessList.remove(waitingProcess)
						#Lo aggiunge alla lista dei processi in esecuzione
						self.memory.processList.append(waitingProcess)
						break

				#Se nessun blocco e' abbastanza grande da contenere il processo
				if IsSmall:
					totalFreeSpace = 0
					greatestBlock = 0

					#L'allocazione e' fallita
					countAllocationFail += 1

					for i in range(0, len(self.memory.freeList)):
						totalFreeSpace += self.memory.freeList[i].size
						if self.memory.freeList[i].size > greatestBlock:
							greatestBlock = self.memory.freeList[i].size

					#E la somma dei blocchi ha una dimensione maggiore di quella richiesta dal processo
					#Allora si parla di frammentazione esterna
					if totalFreeSpace >= waitingProcess.size:
						externalFragmentation = round(((1 - (greatestBlock / totalFreeSpace)) * 100), 2)
						percentExtFrag += externalFragmentation
						countExternalFrag += 1

			#Stampa uno stato della memoria di tipo grafico
			self.graphicStateOfMemory(currentTimer)
			#Incremento l'istante di tempo
			currentTimer += 1

		#Effettuo i calcoli per la grandezza media dei blocchi liberi alla fine dell'esecuzione dell'algoritmo
		sumFreeList = 0
		for i in range(0, len(self.memory.freeList)):
			sumFreeList += self.memory.freeList[i].size

		#La media la effettuo dividendo il totale di spazio libero per il numero di blocchi
		sumFreeList = sumFreeList / len(self.memory.freeList)

		logging.write(Colors.White + "")			

		#Print per il numero di confronti
		logging.write("Numero confronti: " + str(countComparisons))

		#Print del numero di allocazioni fallite, di cui n per colpa della frammentazione esterna
		logging.write("Allocazioni fallite: " + str(countAllocationFail) + ", di cui " + str(countExternalFrag) + " per frammentazione esterna")
		
		#In questa parte effettuiamo il calcolo per la percentuale di frammentazione esterna seguendo la formula
		#FRAMMENTAZIONE ESTERNA = ( 1 - (BLOCCO PIU' GRANDE / TOTALE SPAZIO LIBERO) ) * 100		
		if countExternalFrag > 0:
			percentExtFrag = percentExtFrag / countExternalFrag
		else:
			percentExtFrag = 0
		logging.write("Frammentazione Esterna Media dell'esecuzione: " + str(percentExtFrag) + "%")

		logging.write("")
		logging.write(Colors.BoldYellow + "----------------" + Colors.White)
		logging.write("")	

		return 	sumFreeList, countComparisons, percentExtFrag, countAllocationFail, countExternalFrag

	#Eseguira' l'algoritmo Best-Fit pr l'allocazione dei processi in memoria
	#Verra' scelto il blocco di memoria che sara' di poco superiore alla grandezza del nostro processo
	def bestFit(self):
		#Inizializzo l'orologio, il contatore per i confronti,
		#il contatore di frammentazioni esterne e variabile di calcolo
		currentTimer = 0
		countComparisons = 0
		countAllocationFail = 0
		countExternalFrag = 0
		percentExtFrag = 0
		
		logging.write(Colors.BoldGreen + "Best-Fit")

		#Continuero' l'esecuzione dell'algoritmo finche' ci saranno processi in attesa di entrare in memoria
		while len(self.waitProcessList) > 0:
			#Puliamo la memoria da possibili processi che hanno completato la loro esecuzione
			self.clearMemory()
			#Uniamo gli spazi di memoria vicini
			self.memory.joinMemory()
			#Controllo la freelist per blocchi di memoria non presenti
			self.memory.checkFreeList()
			#Cerco un processo che deve entrare in questo istante di tempo
			processIdx = self.checkForProcesses(currentTimer)
			#Inizio la variabile per la frammentazione esterna
			IsSmall = True

			#Variabili da utilizzare per effettuare il Best-Fit
			bestBlockIdx = -1
			bestBlockSize = 999999

			#Proviamo l'allocazione solo se un processo deve entrare adesso
			if(processIdx != -1):
				#Recuperiamo il processo dalla lista dei processi in attesa
				waitingProcess = self.waitProcessList[processIdx]
				for i in range(0, len(self.memory.freeList)):
					#Incrementiamo il costo del confronto
					countComparisons += 1
					#Se il processo ha una dimensione minore di quella del blocco libero allora...
					if(self.memory.freeList[i].size >= waitingProcess.size):
						#Controllo che il blocco scelto abbia una dimensione minore del blocco migliore fin'ora trovato
						if(self.memory.freeList[i].size < bestBlockSize):
							#Mi memorizzo il suo indice e la sua dimensione
							bestBlockIdx = i
							bestBlockSize = self.memory.freeList[i].size
							#Non e' troppo piccolo per contenere il processo
							IsSmall = False

				#Se ho trovato un blocco adatto al processo
				if(bestBlockIdx != -1):
						#Alloca il processo
						self.allocateProcess(bestBlockIdx, waitingProcess)
						#Rimuove il processo dalla lista dei processi pronti
						self.waitProcessList.remove(waitingProcess)
						#Lo aggiunge alla lista dei processi in esecuzione
						self.memory.processList.append(waitingProcess)

				#Se nessun blocco e' abbastanza grande da contenere il processo
				if IsSmall:
					totalFreeSpace = 0
					greatestBlock = 0

					#L'allocazione e' fallita
					countAllocationFail += 1

					for i in range(0, len(self.memory.freeList)):
						totalFreeSpace += self.memory.freeList[i].size
						if self.memory.freeList[i].size > greatestBlock:
							greatestBlock = self.memory.freeList[i].size

					#E la somma dei blocchi ha una dimensione maggiore di quella richiesta dal processo
					#Allora si parla di frammentazione esterna
					if totalFreeSpace >= waitingProcess.size:
						externalFragmentation = round(((1 - (greatestBlock / totalFreeSpace)) * 100), 2)
						percentExtFrag += externalFragmentation
						countExternalFrag += 1

			#Stampa uno stato della memoria di tipo grafico
			self.graphicStateOfMemory(currentTimer)
			#Incremento l'istante di tempo
			currentTimer += 1

		#Effettuo i calcoli per la grandezza media dei blocchi liberi alla fine dell'esecuzione dell'algoritmo
		sumFreeList = 0
		for i in range(0, len(self.memory.freeList)):
			sumFreeList += self.memory.freeList[i].size

		#La media la effettuo dividendo il totale di spazio libero per il numero di blocchi
		sumFreeList = sumFreeList / len(self.memory.freeList)

		logging.write(Colors.White + "")			

		#Print per il numero di confronti
		logging.write("Numero confronti: " + str(countComparisons))

		#Print del numero di allocazioni fallite, di cui n per colpa della frammentazione esterna
		logging.write("Allocazioni fallite: " + str(countAllocationFail) + ", di cui " + str(countExternalFrag) + " per frammentazione esterna")

		#In questa parte effettuiamo il calcolo per la percentuale di frammentazione esterna seguendo la formula
		#FRAMMENTAZIONE ESTERNA = ( 1 - (BLOCCO PIU' GRANDE / TOTALE SPAZIO LIBERO) ) * 100		
		if countExternalFrag > 0:
			percentExtFrag = percentExtFrag / countExternalFrag
		else:
			percentExtFrag = 0
		logging.write("Frammentazione Esterna Media dell'esecuzione: " + str(percentExtFrag) + "%")

		logging.write("")
		logging.write(Colors.BoldYellow + "----------------" + Colors.White)
		logging.write("")	

		return 	sumFreeList, countComparisons, percentExtFrag, countAllocationFail, countExternalFrag

	#Eseguira' l'algoritmo Worst-Fit pr l'allocazione dei processi in memoria
	#Verra' scelto il blocco di memoria piu' grande in cui il processo puo' entrare
	def worstFit(self):
		#Inizializzo l'orologio, il contatore per i confronti,
		#il contatore di frammentazioni esterne e variabile di calcolo
		currentTimer = 0
		countComparisons = 0
		countAllocationFail = 0
		countExternalFrag = 0
		percentExtFrag = 0

		logging.write(Colors.BoldBlue + "Worst-Fit")

		#Continuero' l'esecuzione dell'algoritmo finche' ci saranno processi in attesa di entrare in memoria
		while len(self.waitProcessList) > 0:
			#Puliamo la memoria da possibili processi che hanno completato la loro esecuzione
			self.clearMemory()
			#Uniamo gli spazi di memoria vicini
			self.memory.joinMemory()
			#Controllo la freelist per blocchi di memoria non presenti
			self.memory.checkFreeList()
			#Cerco un processo che deve entrare in questo istante di tempo
			processIdx = self.checkForProcesses(currentTimer)
			#Inizio la variabile per la frammentazione esterna
			IsSmall = True

			#Variabili da utilizzare per effettuare il Worst-Fit
			worstBlockIdx = -1
			worstBlockSize = 0

			#Proviamo l'allocazione solo se un processo deve entrare adesso
			if(processIdx != -1):
				#Recuperiamo il processo dalla lista dei processi in attesa
				waitingProcess = self.waitProcessList[processIdx]
				for i in range(0, len(self.memory.freeList)):
					#Incrementiamo il costo del confronto
					countComparisons += 1
					#Se il processo ha una dimensione minore di quella del blocco libero allora...
					if(self.memory.freeList[i].size >= waitingProcess.size):
						#Controllo che il blocco scelto abbia una dimensione maggiore del blocco migliore fin'ora trovato
						if(self.memory.freeList[i].size > worstBlockSize):
							#Mi memorizzo il suo indice e la sua dimensione
							worstBlockIdx = i
							worstBlockSize = self.memory.freeList[i].size
							#Non e' troppo piccolo per contenere il processo
							IsSmall = False

				#Se ho trovato un blocco adatto al processo
				if(worstBlockIdx != -1):
						#Alloca il processo
						self.allocateProcess(worstBlockIdx, waitingProcess)
						#Rimuove il processo dalla lista dei processi pronti
						self.waitProcessList.remove(waitingProcess)
						#Lo aggiunge alla lista dei processi in esecuzione
						self.memory.processList.append(waitingProcess)

				#Se nessun blocco e' abbastanza grande da contenere il processo
				if IsSmall:
					totalFreeSpace = 0
					greatestBlock = 0

					#L'allocazione e' fallita
					countAllocationFail += 1

					for i in range(0, len(self.memory.freeList)):
						totalFreeSpace += self.memory.freeList[i].size
						if self.memory.freeList[i].size > greatestBlock:
							greatestBlock = self.memory.freeList[i].size

					#E la somma dei blocchi ha una dimensione maggiore di quella richiesta dal processo
					#Allora si parla di frammentazione esterna
					if totalFreeSpace >= waitingProcess.size:
						externalFragmentation = round(((1 - (greatestBlock / totalFreeSpace)) * 100), 2)
						percentExtFrag += externalFragmentation
						countExternalFrag += 1

			#Stampa uno stato della memoria di tipo grafico
			self.graphicStateOfMemory(currentTimer)
			#Incremento l'istante di tempo
			currentTimer += 1

		#Effettuo i calcoli per la grandezza media dei blocchi liberi alla fine dell'esecuzione dell'algoritmo
		sumFreeList = 0
		for i in range(0, len(self.memory.freeList)):
			sumFreeList += self.memory.freeList[i].size

		#La media la effettuo dividendo il totale di spazio libero per il numero di blocchi
		sumFreeList = sumFreeList / len(self.memory.freeList)

		logging.write(Colors.White + "")			

		#Print per il numero di confronti
		logging.write("Numero confronti: " + str(countComparisons))

		#Print del numero di allocazioni fallite, di cui n per colpa della frammentazione esterna
		logging.write("Allocazioni fallite: " + str(countAllocationFail) + ", di cui " + str(countExternalFrag) + " per frammentazione esterna")

		#In questa parte effettuiamo il calcolo per la percentuale di frammentazione esterna seguendo la formula
		#FRAMMENTAZIONE ESTERNA = ( 1 - (BLOCCO PIU' GRANDE / TOTALE SPAZIO LIBERO) ) * 100		
		if countExternalFrag > 0:
			percentExtFrag = percentExtFrag / countExternalFrag
		else:
			percentExtFrag = 0
		logging.write("Frammentazione Esterna Media dell'esecuzione: " + str(percentExtFrag) + "%")

		logging.write("")
		logging.write(Colors.BoldYellow + "----------------" + Colors.White)
		logging.write("")	

		return 	sumFreeList, countComparisons, percentExtFrag, countAllocationFail, countExternalFrag

	#Effettuiamo la pulizia della memoria prima di eseguire un allocazione
	def clearMemory(self):
		countMemoryBlocks = len(self.memory.memoryBlocks)
		i = 0

		while i < countMemoryBlocks:
			currentProcess = None
			currentProcessIdx = None

			#Se il blocco corrente e' allocato...
			if(self.memory.memoryBlocks[i].isAllocated):
				for k in range(0, len(self.memory.processList)):
					#Cerco a quale processo e' associato
					if(self.memory.memoryBlocks[i] == self.memory.processList[k].block):
						currentProcess = self.memory.processList[k]
						currentProcessIdx = k

				#Se non c'e' un processo che corrisponde a quel blocco, errore!
				if(currentProcessIdx == None):
					raise Exception("Error! No process allocated!")

				#Diminuisco il tempo di lavoro del processo
				currentProcess.workingTime -= 1

				#Se il suo tempo di lavoro e' arrivato a 0
				if(currentProcess.workingTime == 0):
					#Rilascio il processo e la memoria da lui occupata
					self.memory.processList.remove(currentProcess)			
					self.memory.memoryBlocks[i].isAllocated = False
			i += 1

	#Cerco un processo che ha come tempo di entrata quello corrente
	def checkForProcesses(self, currentTimer):
		for i in range(0, len(self.waitProcessList)):
			if(self.waitProcessList[i].startTime <= currentTimer):
				return i
		return -1

	#Alloco il processo sul blocco di memoria
	def allocateProcess(self, freeListIdx, process):
		memoryBlock = self.memory.freeList[freeListIdx]

		#Se il processo ci sta perfettamente, lo assegno semplicemente all'intero blocco
		if memoryBlock.size == process.size:
			memoryBlock.isAllocated = True
			process.block = memoryBlock
			self.memory.freeList.remove(memoryBlock)
		else:
			#Effettuo lo split del blocco di memoria
			newBlock = self.memory.splitMemory(memoryBlock, process.size)
			newBlock.isAllocated = True
			process.block = newBlock

	#Controllo sui blocchi di memoria per sapere se sono allocati
	def isMemoryAllocated(self):
		for i in range(0, len(self.memory.memoryBlocks)):
			if(self.memory.memoryBlocks[i].isAllocated):
				return True
		return False

	#Print grafico della memoria in ogni istante di tempo
	def graphicStateOfMemory(self, currentTimer):
		graph = Colors.DarkGray + str(currentTimer).zfill(4) + Colors.White + " - "
		for i in range(0, len(self.memory.memoryBlocks)):
			graph += Colors.LightGray + "|"
			#Se il blocco e' allocato, allora stampo T
			if(self.memory.memoryBlocks[i].isAllocated):
				graph += Colors.BoldRed
				graph += str(self.memory.memoryBlocks[i].size)
				graph += "T"
			#Altrimenti stampo F
			else:
				graph += Colors.BoldGreen
				graph += str(self.memory.memoryBlocks[i].size)
				graph += "F"

		graph += Colors.LightGray + "|"

		self.logging.write(graph)


#Inizializzo la classe LOG con un nome del file, e permessi di append
logging = Log("log", "a")

logging.write(Colors.White + datetime.datetime.now().strftime('Simulazione effettuata in data %d/%m/%Y alle ore %H:%M:%S'))

#Viene fatto un controllo se e' stato passato un argomento, ed in caso,
#Avvia le simulazioni in base all'argomento. Altrimenti verra' richiesto
#l'input da shell del numero di simulazioni
if(len(sys.argv) > 1):
	simulationsNumber = int(sys.argv[1])
else:
	print Colors.White + "Inserire il numero di simulazioni che si vogliono effettuare: "
	simulationsNumber = int(input());

logging.write(Colors.White + "Numero di simulazioni scelto: " + str(simulationsNumber))

#Inizializzo le variabili di statistica finali
mediaFreeBlocksFF = 0
mediaFreeBlocksBF = 0
mediaFreeBlocksWF = 0

mediaCompareFF = 0
mediaCompareBF = 0
mediaCompareWF = 0

mediaExtFragFF = 0 
mediaExtFragBF = 0
mediaExtFragWF = 0

countAllocFailFF = 0
countAllocFailBF = 0
countAllocFailWF = 0

countExtFragFF = 0
countExtFragBF = 0
countExtFragWF = 0

#Dichiaro delle costanti per le inizializzazioni che avverranno sulla memoria / processi
memorySize = 16384

minNumProcess = 32
maxNumProcess = 64

minProcessSize = 1024
maxProcessSize = 3096

minWorkTime = 4
maxWorkTime = 16

minStartTime = 1
maxStartTime = 4

#Ripeto l'intero ciclo per il numero di simulazioni da me scelto
for i in range(0, simulationsNumber):

	logging.write(Colors.White + "Inizio simulazione numero " + str(i+1))
	logging.write("")

	#Inizializzo la memoria con una dimensione fissa
	originalMemoryStatus = Memory(memorySize, logging)

	#Scegliamo il numero di processi su cui vogliamo effettuare la simulazione
	processNumber = random.randint(minNumProcess, maxNumProcess)

	originalProcessesStatus = []

	#Il primo processo entrera' a tempo 0
	currentStartTime = 0

	logging.write(Colors.BoldRed + "Process\tSize\tStartTime\tWorkTime")

	#Inizializzo i processi con dei valori di base
	for i in range(0, processNumber):
		#Dimensione del processo
		processSize = random.randint(minProcessSize, maxProcessSize)
		#Worktime per il processo
		workTime = random.randint(minWorkTime, maxWorkTime)
		#Inizializzo il processo senza nessun blocco di memoria, poiche' non ancora allocato
		originalProcessesStatus.append(Process(processSize, None, currentStartTime, workTime))

		logging.write(Colors.White + str(i)+"\t"+str(processSize)+"\t"+str(currentStartTime)+"\t"+"\t"+str(workTime))

		#Calcolo il tempo d'entrata per il prossimo processo
		currentStartTime += random.randint(minStartTime, maxStartTime)

	logging.write("")
	logging.write("")

	#Ripeto il ciclo per i 3 algoritmi
	for i in range(0, 3):
		#Copia locale della memoria
		memory = copy.deepcopy(originalMemoryStatus)
		#Copia locale dei processi in attesa
		process = copy.deepcopy(originalProcessesStatus)

		#Inizializzo l'allocatore
		allocator = AllocationManager(memory, process, logging)

		#First-Fit
		if(i == 0):
			#temp0-4 conterranno i valori che ritorneremo dalla funzione
			temp0, temp1, temp2, temp3, temp4 = allocator.firstFit()
			mediaFreeBlocksFF += temp0
			mediaCompareFF += temp1
			mediaExtFragFF += temp2
			countAllocFailFF += temp3
			countExtFragFF += temp4
		#Best-Fit
		elif(i == 1):
			#temp0-4 conterranno i valori che ritorneremo dalla funzione
			temp0, temp1, temp2, temp3, temp4 = allocator.bestFit()
			mediaFreeBlocksBF += temp0
			mediaCompareBF += temp1
			mediaExtFragBF += temp2
			countAllocFailBF += temp3
			countExtFragBF += temp4
		#Worst-Fit
		elif(i == 2):
			#temp0-4 conterranno i valori che ritorneremo dalla funzione
			temp0, temp1, temp2, temp3, temp4 = allocator.worstFit()
			mediaFreeBlocksWF += temp0
			mediaCompareWF += temp1
			mediaExtFragWF += temp2
			countAllocFailWF += temp3
			countExtFragWF += temp4

		#Resetto l'allocatore a None
		allocator = None

#Calcolo la media in base al numero di simulazioni effettuate
mediaFreeBlocksFF /= simulationsNumber
mediaFreeBlocksBF /= simulationsNumber
mediaFreeBlocksWF /= simulationsNumber

mediaCompareFF /= simulationsNumber
mediaCompareBF /= simulationsNumber
mediaCompareWF /= simulationsNumber

mediaExtFragFF /= simulationsNumber
mediaExtFragBF /= simulationsNumber
mediaExtFragWF /= simulationsNumber

#Print delle varie statistiche ottenute dalle simulazioni

logging.write(Colors.BoldBlue + "Risultati finali ottenuti dalle simulazioni")

logging.write("")
logging.write(Colors.BoldYellow + "----------------" + Colors.White)
logging.write(Colors.White + "")

logging.write("Media dimensione blocchi liberi First-Fit: " + str(int(mediaFreeBlocksFF)))
logging.write("Media dimensione blocchi liberi Best-Fit: " + str(int(mediaFreeBlocksBF)))
logging.write("Media dimensione blocchi liberi Worst-Fit: " + str(int(mediaFreeBlocksWF)))

logging.write("")

logging.write("Media confronti First-Fit: " + str(int(mediaCompareFF)))
logging.write("Media confronti Best-Fit: " + str(int(mediaCompareBF)))
logging.write("Media confronti Worst-Fit: " + str(int(mediaCompareWF)))

logging.write("")

logging.write("Numero di allocazioni fallite First-Fit: " + str(int(countAllocFailFF)) + ", di cui " +  str(int(countExtFragFF)) + " per via della frammentazione esterna")
logging.write("Numero di allocazioni fallite Best-Fit: " + str(int(countAllocFailBF)) + ", di cui " +  str(int(countExtFragBF)) + " per via della frammentazione esterna")
logging.write("Numero di allocazioni fallite Worst-Fit: " + str(int(countAllocFailWF)) + ", di cui " +  str(int(countExtFragWF)) + " per via della frammentazione esterna")
logging.write("")

logging.write("Media di frammentazione esterna First-Fit (%): " + str(round(mediaExtFragFF, 2)) + "%")
logging.write("Media di frammentazione esterna Best-Fit (%): " + str(round(mediaExtFragBF, 2)) + "%")
logging.write("Media di frammentazione esterna Worst-Fit (%): " + str(round(mediaExtFragWF, 2)) + "%")


logging.write("")
logging.write("")
logging.write(Colors.BoldYellow + "-------------------------------------------------------")
logging.write("")
logging.write("")

print Colors.Default