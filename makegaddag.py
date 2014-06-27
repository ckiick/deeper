#!/usr/bin/python
# By Steve Hanov, 2011. Released to the public domain.
# extensivley modded by  ckiick 2014

import sys
import time
from collections import deque
import struct

if len(sys.argv) > 1:
    DICTIONARY = sys.argv[1]
else:
    DICTIONARY = "words.txt"


if len(sys.argv) > 2:
    BINFILE = sys.argv[2]
else:
    BINFILE = "makegaddag.bin"

#QUERY = sys.argv[1:]

# This class represents a node in the directed acyclic word graph (DAWG). It
# has a list of edges to other nodes. It has functions for testing whether it
# is equivalent to another node. Nodes are equivalent if they have identical
# edges, and each identical edge leads to identical states. The __hash__ and
# __eq__ functions allow it to be used as a key in a python dictionary.
class DawgNode:
    NextId = 0
    NextNdx = 0
    NewNdx = 0

    def __init__(self):
        self.id = DawgNode.NextId
        DawgNode.NextId += 1
        self.final = False
        self.edges = {}
	self.index = -1
	self.arcindex = -1

    def __str__(self):        
        arr = []
        if self.final: 
            arr.append("1")
        else:
            arr.append("0")

        for (label, node) in self.edges.iteritems():
            arr.append( label )
            arr.append( str( node.id ) )

        return "_".join(arr)

    def __hash__(self):
        return self.__str__().__hash__()

    def __eq__(self, other):
        return self.__str__() == other.__str__()

    def __dmp__(self):
        str = "%d:%d" % ( self.index, self.id )
	if (self.final): str += "/f"
	str += "->S[%d]=" % ( len(self.edges) )
        for (label, cnode) in self.edges.iteritems():
            str += "[%c,%d]" % ( label, cnode.id )
	return str


# this class represents an edge or arc in the gaddag.
class Arc:
    NextCtr = 0

    def __init__(self):
	self.nodeid = 0
	self.index = -1
	self.letter = "~"
	self.eow = False
	self.eos = False
	self.cid = -1
	self.cindex = -1

    def __tostr__ (self):
	arcstr = ""
	arcstr += str(self.index) + ":" + str(self.cindex) + "|"
	if self.eos:
	    arcstr += "$|"
	else:
	    arcstr += ">|"

        if self.eow:
	    arcstr += ".|"
	else:
	    arcstr += " |"

	arcstr += self.letter
	return arcstr

    def __tobin__( self ):
	word = self.cindex << 8
	if self.eos:
	    word |= 0x80

        if self.eow:
	    word |= 0x40

	word |= (0x3F & ord(self.letter[0]))

	return word

class Dawg:
    def __init__(self):
        self.previousWord = ""
        self.root = DawgNode()
	self.queue = deque()

        # Here is a list of nodes that have not been checked for duplication.
        self.uncheckedNodes = []

        # Here is a list of unique nodes that have been checked for
        # duplication.
        self.minimizedNodes = {}

	# and this is the list for the compressed output
	self.indexed = []

    def insert( self, word ):
        if word < self.previousWord:
            raise Exception("Error: Words must be inserted in alphabetical " +
                "order.")

        # find common prefix between word and previous word
        commonPrefix = 0
        for i in range( min( len( word ), len( self.previousWord ) ) ):
            if word[i] != self.previousWord[i]: break
            commonPrefix += 1

        # Check the uncheckedNodes for redundant nodes, proceeding from last
        # one down to the common prefix size. Then truncate the list at that
        # point.
        self._minimize( commonPrefix )

        # add the suffix, starting from the correct node mid-way through the
        # graph
        if len(self.uncheckedNodes) == 0:
            node = self.root
        else:
            node = self.uncheckedNodes[-1][2]

        for letter in word[commonPrefix:]:
            nextNode = DawgNode()
            node.edges[letter] = nextNode
            self.uncheckedNodes.append( (node, letter, nextNode) )
            node = nextNode

        node.final = True
        self.previousWord = word

    def finish( self ):
        # minimize all uncheckedNodes
        self._minimize( 0 );

    def _minimize( self, downTo ):
        # proceed from the leaf up to a certain point
        for i in range( len(self.uncheckedNodes) - 1, downTo - 1, -1 ):
            (parent, letter, child) = self.uncheckedNodes[i];
            if child in self.minimizedNodes:
                # replace the child with the previously encountered one
                parent.edges[letter] = self.minimizedNodes[child]
            else:
                # add the state to the minimized nodes.
                self.minimizedNodes[child] = child;
            self.uncheckedNodes.pop()

    def dumproot( self ):
	return self.root.__dmp__()


    def lookup( self, word ):
        node = self.root
        for letter in word:
            if letter not in node.edges: return False
            node = node.edges[letter]

        return node.final

    def nodeCount( self ):
        return len(self.minimizedNodes)

    def edgeCount( self ):
        count = 0
        for node in self.minimizedNodes:
            count += len(node.edges)
        return count

    def makeIndex( self ):
	self.queue.append(self.root)
	while len(self.queue) > 0:
		node = self.queue.popleft()
		if node.index != -1: continue
        	node.index = DawgNode.NextNdx
        	DawgNode.NextNdx += len(node.edges)
		for l in sorted(node.edges.keys()):
			self.queue.append(node.edges[l])
	print str(DawgNode.NextNdx)

    def reindex ( self, node ):
	if (node.arcindex != -1): return
	n = DawgNode.NewNdx
	letters = sorted(node.edges.keys())
	for i, l in enumerate(letters):
	    newarc = Arc()
	    newarc.index = n + i
	    newarc.letter = l
	    newarc.nodeid = node.id
	    newarc.eow = node.edges[l].final
	    newarc.eos = (i == (len(node.edges)-1))
	    newarc.cid = node.edges[l].id
	    self.indexed.append(newarc)

	node.arcindex = n
	DawgNode.NewNdx += len(node.edges)
	for l in letters:
	    self.reindex ( node.edges[l] )

	for i, l in enumerate(letters):
	    self.indexed[n+i].cindex = node.edges[l].arcindex

	return DawgNode.NewNdx

    def barf( self ):
        yf.write(self.root.__str__() + "\n")
        for node in self.minimizedNodes:
            yf.write(node.__str__() + "\n")


    def dump( self ):
        df.write(self.root.__dmp__() + "\n")
        for node in self.minimizedNodes:
            df.write(node.__dmp__() + "\n")

    def spew( self ):
	for arc in self.indexed:
	   sf.write(arc.__tostr__() + "\n")

    def dobin( self ):
	binned = []
	for arc in self.indexed:
	    binned.append(arc.__tobin__())
        bf.write(struct.pack('%sI' % len(binned), *binned))


dawg = Dawg()
WordCount = 0
words = open(DICTIONARY, "rt").read().split()
words.sort()
print "Staring Dawg creation..."
start = time.time()    
for word in words:
    WordCount += 1
    dawg.insert(word)
#    if ( WordCount % 1000 ) == 0: print "$dr" % WordCount,
dawg.finish()
print "Dawg creation took %g s" % (time.time()-start)    

EdgeCount = dawg.edgeCount()
print "Read %d words into %d nodes and %d edges" % ( WordCount,
        dawg.nodeCount(), EdgeCount )
#print "This could be stored in as little as %d bytes" % (EdgeCount * 4)    

print "indexing... "
dawg.makeIndex()
print "done"

print "dumping..."
df = open("makegaddag.dump", "wt")
dawg.dump()
print "...done"

print "barfing..."
yf = open("makegaddag.barf", "wt")
dawg.barf()
print "....done"

print "compressing to binary gaddag..."
bincount = dawg.reindex(dawg.root)
bf = open(BINFILE, "wt")
dawg.dobin()
print "compressed %d arcs to %d bytes\n" % (bincount, bincount*4)
print "...done"

print "spewing..."
sf = open("makegaddag.spew", "wt")
dawg.spew()
print "...done"

print "looking up stuff "
QUERY=["FOZY", "YZOF", "FOZYNG", "GNFOZY", "NGFOZY", "YZOFNG", "YZOFGN"]

for word in QUERY:
    if not dawg.lookup( word ):
        print "%s not in dictionary." % word
    else:
        print "%s is in the dictionary." % word


print "root node is %s." % dawg.dumproot()
