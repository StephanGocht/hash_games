import sys
import io

import math
import random

import itertools
import argparse

class BitVec(object):
    def __init__(self, numBits):
        pass


def nextInt32(it):
    result = []
    for i in range(4):
        result.append(next(it))
    return int.from_bytes(result, byteorder='big')

class TrueBits(object):
    def __init__(self, data):
        self.data = iter(data)

    def blocks(self):
        while True:
            w = []
            for i in range(16):
                try:
                    w.append(nextInt32(self.data))
                except StopIteration:
                    return
            yield w

    def leftrotate(self, n, value):
        assert(value > 0)
        mask32bit = 0xFFFFFFFF
        return (n << value | n >> (32 - value)) & mask32bit

    def bitwise_if(self, b,c,d):
        return (b & c) | ((~b) & d)

    def bitwise_xor(self, *args):
        result = 0
        for i in args:
            result ^= i
        return result

    def bitsum32(self, *args):
        mask32bit = 0xFFFFFFFF

        result = 0
        for i in args:
            result += i

        return result & mask32bit

    def bitwise_mayority(self, b,c,d):
        return (b & c) | (b & d) | (c & d)

    def constant(self, value, nBits):
        return value

class Formula(object):
    def __init__(self, outputFile):
        self.outputFile = outputFile
        self.maxVar = 0
        self.format = format
        self.nConstraints = 0

    def var(self, i):
        raise NotImplementedError()

    def _isEnd(self, char):
        raise NotImplementedError()

    def _header(self):
        raise NotImplementedError()

    def newVar(self):
        self.maxVar += 1
        return self.var(self.maxVar)

    def newVars(self, n):
        result = []

        for i in range(n):
            result.append(self.newVar())

        return result


    def print(self, *args, **kwargs):
        if self.outputFile:
            kwargs["file"] = self.outputFile
            print(*args, **kwargs)

            if len(args) > 0 and len(args[-1]) > 0 and self._isEnd(args[-1][-1]):
                self.nConstraints += 1

    def writeHeader(self):
        pos = self.outputFile.tell()
        self.outputFile.seek(0)
        self._header()
        self.outputFile.seek(pos)


class OPBFormula(Formula):
    def var(self, i):
        return "x%i"%(i)

    def _isEnd(self, char):
        return char == ";"

    def _header(self):
        self.print("* #variable= %i #constraint= %i" % (self.maxVar, self.nConstraints), end = "")

class CNFFormula(Formula):
    def var(self, i):
        return "%i"%(i)

    def _isEnd(self, char):
        return char == ";"

    def _header(self):
        self.print("p cnf %i %i" % (self.maxVar, self.nConstraints), end = "")


class CNFBits(object):
    def __init__(self, formula, num_chunks):
        self.inputVars = None
        self.num_chunks = num_chunks
        self.formula = formula

        # reserve space for header
        self.print(" " * 100)

    def newVars(self, n):
        return self.formula.newVars(n)

    def print(self, *args, **kwargs):
        self.formula.print(*args,**kwargs)

    def getInBits(self):
        if self.inputVars is None:
            self.inputVars = self.newVars(512 * self.num_chunks)
        return self.inputVars

    def blocks(self):
        bits = self.getInBits()
        self.data = iter(bits)

        while True:
            w = []
            for i in range(16):
                try:
                    w.append([next(self.data) for i in range(32)])
                except StopIteration:
                    return
            yield w

    def leftrotate(self, n, value):
        return n[value:] + n[:value]

    def bitwise_if(self, b, c, d):
        # (b & c) | ((~b) & d)
        assert(len(b) == len(c) and len(c) == len(d))
        res = self.newVars(len(b))

        # clausal encoding after

        # SAT-based preimage attacks on SHA-1
        # Vegard Nossum
        # November, 2012

        # Eén, N. and Biere, A. (2005). Effective preprocessing in SAT through variable and
        # clause elimination. In SAT ’05: Proceedings of the 8th International Conference
        # on Theory and Applications of Satisfiability Testing vol. 3569, of LNCS pp. 61–75,
        # Springer-Verlag Berlin Heidelberg.
        for x,y,z,f in zip(b,c,d,res):
            clauses = [
                [(0,f), (0,x), (1,y)],
                [(0,f), (1,x), (1,z)],
                [(0,f), (1,y), (1,z)],
                [(1,f), (0,x), (0,y)],
                [(1,f), (1,x), (0,z)],
                [(1,f), (0,y), (0,z)]
            ]
            for clause in clauses:
                for sign, var in clause:
                    self.print("%s%s "%("-" if not sign else "", var), end = "")
                self.print("0")

        return res

    def bitwise_xor(self, *args):
        res = self.newVars(len(args[0]))
        for arg in args:
            assert(len(arg) == len(res))

        variables = list(args)
        variables.append(res)

        for variables in zip(*variables):
            for values in itertools.product([0,1], repeat = len(args)):
                values = list(values)
                values.append((sum(values) + 1) % 2)

                for sign, var in zip(values, variables):
                    self.print("%s%s "%("-" if sign else "", var), end = "")
                self.print("0")

        return res

    adderMap = None
    def getAdderMap(self):
        if self.adderMap is None:
            self.adderMap = dict()
            for i,j in [(2,2), (3,2), (5,3), (6,3), (7,3)]:
                fileName = "sha1-sat/data/halfadder-%i-%i.out.txt"
                with open(fileName%(i,j), "r") as file:
                    res = list()
                    for line in file:
                        words = line.strip().split(" ")
                        if len(words) > 0:
                            if words[0] in [".i", ".o", ".p", ".e", ""]:
                                continue
                            res.append(words[0])
                            assert(len(res[-1]) == i + j)
                self.adderMap[(i,j)] = res

        return self.adderMap

    def halfAdder(self, *args):
        nBits = len(args)
        nOutBits = math.floor(math.log2(nBits)) + 1
        outVars = self.newVars(nOutBits)
        clauses = self.getAdderMap()[(nBits, nOutBits)]

        variables = list(args) + list(reversed(outVars))
        for clause in clauses:
            for val, var in zip(clause, variables):
                if val == "0":
                    self.print("-", end = "")
                if val != "-":
                    self.print("%s " % (var), end = "")

            self.print("0")

        return list(enumerate(outVars))

    def bitsum32(self, *args):
        nBits = len(args[0])
        nArgs = len(args)
        nOut  = math.ceil(math.log2( nArgs * (2 ** nBits - 1) ))
        result = list()

        for arg in args:
            assert(len(arg) == nBits)

        addands = list()
        for i in range(nOut):
            addands.append(list())

        for arg in args:
            for i, var in enumerate(reversed(arg)):
                addands[i].append(var)

        for i in range(nBits):
            added = self.halfAdder(*addands[i])
            j, var = added[0]
            assert(j == 0)
            result.append(var)
            for j, var in added[1:]:
                addands[i + j].append(var)

        return list(reversed(result))

    def bitwise_mayority(self, b, c, d):
        nBits = len(b)
        result = self.newVars(nBits)
        # for b, c, d, r in zip(b,c,d,result):
        #     self.print("1 %s 1 %s 1 %s 2 ~%s >= 2 ;" % (b,c,d,r))
        #     self.print("1 ~%s 1 ~%s 1 ~%s 2 %s >= 2 ;" % (b,c,d,r))


        for x,y,z,f in zip(b,c,d,result):
            clauses = [
                [(0,f), (1,x), (1,y)],
                [(0,f), (1,x), (1,z)],
                [(0,f), (1,y), (1,z)],
                [(1,f), (0,x), (0,y)],
                [(1,f), (0,x), (0,z)],
                [(1,f), (0,y), (0,z)],
            ]
            for clause in clauses:
                for sign, var in clause:
                    self.print("%s%s "%("-" if not sign else "", var), end = "")
                self.print("0")

        return result

    def constant(self, value, nBits):
        result = self.newVars(nBits)
        self.setVars(value, result)
        return result

    def setVars(self, value, variables):
        nBits = len(variables)
        mask = 1 << nBits
        for var in variables:
            mask >>= 1
            val = bool(value & mask)
            # self.print("1 %s%s >= 1 ;"%("" if val else "~", var))
            self.print("%s%s 0"%("" if val else "-", var))


class PBBits(object):
    def __init__(self, formula, num_chunks):
        self.num_chunks = num_chunks
        self.inputVars = None
        self.formula = formula

        # reserve space for header
        self.print(" " * 100)

    def newVars(self, n):
        return self.formula.newVars(n)

    def print(self, *args, **kwargs):
        self.formula.print(*args,**kwargs)

    def getInBits(self):
        if self.inputVars is None:
            self.inputVars = self.newVars(512 * self.num_chunks)
        return self.inputVars

    def blocks(self):
        bits = self.getInBits()
        self.data = iter(bits)

        while True:
            w = []
            for i in range(16):
                try:
                    w.append([next(self.data) for i in range(32)])
                except StopIteration:
                    return
            yield w

    def leftrotate(self, n, value):
        return n[value:] + n[:value]

    def bitwise_if(self, b, c, d):
        # (b & c) | ((~b) & d)
        assert(len(b) == len(c) and len(c) == len(d))
        res = self.newVars(len(b))
        # for variables in zip(b,c,d,res):
        #     truthtable = [
        #         (0,0,0,1),
        #         (0,0,1,0),
        #         (0,1,0,1),
        #         (0,1,1,0),
        #         (1,0,0,1),
        #         (1,0,1,1),
        #         (1,1,0,0),
        #         (1,1,1,0),
        #     ]
        # for variables in zip(res, b, c, d):
        #         for var, val in zip(variables,values):
        #             self.print("1 %s%s "%("~" if val else "",var), end = "")

        #         self.print(">= 1 ;")


        # clausal encoding after

        # SAT-based preimage attacks on SHA-1
        # Vegard Nossum
        # November, 2012

        # Eén, N. and Biere, A. (2005). Effective preprocessing in SAT through variable and
        # clause elimination. In SAT ’05: Proceedings of the 8th International Conference
        # on Theory and Applications of Satisfiability Testing vol. 3569, of LNCS pp. 61–75,
        # Springer-Verlag Berlin Heidelberg.
        for x,y,z,f in zip(b,c,d,res):
            clauses = [
                [(0,f), (0,x), (1,y)],
                [(0,f), (1,x), (1,z)],
                [(0,f), (1,y), (1,z)],
                [(1,f), (0,x), (0,y)],
                [(1,f), (1,x), (0,z)],
                [(1,f), (0,y), (0,z)]
            ]
            for clause in clauses:
                for sign, var in clause:
                    self.print("1 %s%s "%("~" if not sign else "", var), end = "")
                self.print(">= 1 ;")

        return res

    def bitwise_xor(self, *args):
        res = self.newVars(len(args[0]))
        for arg in args:
            assert(len(arg) == len(res))

        variables = list(args)
        variables.append(res)

        # for variables in zip(*variables):
        #     for values in itertools.product([0,1], repeat = len(args)):
        #         values = list(values)
        #         values.append((sum(values) + 1) % 2)

        #         for sign, var in zip(values, variables):
        #             self.print("1 %s%s "%("~" if sign else "", var), end = "")
        #         self.print(">= 1 ;")

        for variables in zip(*variables):
            for var in variables:
                self.print("1 %s " % (var), end = "")

            nHelper = math.floor(len(variables) / 2)
            helperVars = self.newVars(nHelper)

            for var in helperVars:
                self.print("-2 %s " % (var), end = "")

            self.print("= 0 ;")

        return res

    def bitsum32(self, *args):
        nBits = len(args[0])
        nArgs = len(args)
        nOut  = math.ceil(math.log2( nArgs * (2 ** nBits - 1) ))
        result = self.newVars(nOut)

        for arg in args:
            for i, var in enumerate(reversed(arg)):
                self.print("%i %s "%(2**i, var), end = "")

        for i, var in enumerate(reversed(result)):
            self.print("%i %s "%(-2**i, var), end = "")

        self.print("= 0 ;")

        return result[-nBits:]

    def bitwise_mayority(self, b, c, d):
        nBits = len(b)
        result = self.newVars(nBits)
        # for b, c, d, r in zip(b,c,d,result):
        #     self.print("1 %s 1 %s 1 %s 2 ~%s >= 2 ;" % (b,c,d,r))
        #     self.print("1 ~%s 1 ~%s 1 ~%s 2 %s >= 2 ;" % (b,c,d,r))


        for x,y,z,f in zip(b,c,d,result):
            clauses = [
                [(0,f), (1,x), (1,y)],
                [(0,f), (1,x), (1,z)],
                [(0,f), (1,y), (1,z)],
                [(1,f), (0,x), (0,y)],
                [(1,f), (0,x), (0,z)],
                [(1,f), (0,y), (0,z)],
            ]
            for clause in clauses:
                for sign, var in clause:
                    self.print("1 %s%s "%("~" if not sign else "", var), end = "")
                self.print(">= 1 ;")

        return result

    def constant(self, value, nBits):
        result = self.newVars(nBits)
        self.setVars(value, result)
        return result

    def setVars(self, value, variables):
        nBits = len(variables)
        mask = 1 << nBits
        for var in variables:
            mask >>= 1
            val = bool(value & mask)
            # self.print("1 %s%s >= 1 ;"%("" if val else "~", var))
            self.print("1 %s = %i ;"%(var, 1 if val else 0))

def process(bt):
    h = [
            bt.constant(0x67452301, 32),
            bt.constant(0xEFCDAB89, 32),
            bt.constant(0x98BADCFE, 32),
            bt.constant(0x10325476, 32),
            bt.constant(0xC3D2E1F0, 32),
        ]

    for w in bt.blocks():
        for i in range(16, 80):
            tmp = bt.bitwise_xor(w[i-3], w[i-8], w[i-14], w[i-16])
            tmp = bt.leftrotate(tmp, 1)
            w.append(tmp)

        # initialize hash value
        a = h[0]
        b = h[1]
        c = h[2]
        d = h[3]
        e = h[4]

        kall = [
            bt.constant(0x5A827999, 32),
            bt.constant(0x6ED9EBA1, 32),
            bt.constant(0x8F1BBCDC, 32),
            bt.constant(0xCA62C1D6, 32),
        ]

        for i in range(80):
            if i in range(0, 20):
                f = bt.bitwise_if(b, c, d)
                k = kall[0]
            elif i in range(20, 40):
                f = bt.bitwise_xor(b, c, d)
                k = kall[1]
            elif i in range(40, 60):
                f = bt.bitwise_mayority(b, c, d)
                k = kall[2]
            elif i in range(60, 80):
                f = bt.bitwise_xor(b, c, d)
                k = kall[3]

            temp = bt.leftrotate(a, 5)
            temp = bt.bitsum32(temp, f, e, k, w[i])
            e = d
            d = c
            c = bt.leftrotate(b, 30)
            b = a
            a = temp

        h[0] = bt.bitsum32(h[0], a)
        h[1] = bt.bitsum32(h[1], b)
        h[2] = bt.bitsum32(h[2], c)
        h[3] = bt.bitsum32(h[3], d)
        h[4] = bt.bitsum32(h[4], e)

    return h

def prepare(data):
    message_length = len(data) * 8

    data.append(0x80)

    bytes_per_block = (512 // 8)
    used_bytes = message_length//8 + 1 + 8
    to_add = (bytes_per_block - used_bytes) % bytes_per_block

    data.extend([0] * to_add)
    data.extend(message_length.to_bytes(8, byteorder='big'))
    assert(len(data) % bytes_per_block == 0)

    return data

def join(h):
    result = 0
    result = result << 32 | h[0]
    result = result << 32 | h[1]
    result = result << 32 | h[2]
    result = result << 32 | h[3]
    result = result << 32 | h[4]
    return result

def readSolution(solutionFile):
    values = dict()
    for line in solutionFile:
        words = line.strip().split(" ")
        if words[0] == "v":
            for i, lit in enumerate(words[1:]):
                value = True
                if lit[0] == "-":
                    value = False
                    var = lit[1:]
                else:
                    var = lit

                assert(var == "x%i"%(i + 1))
                values[var] = value

    return values

def readSolutionCnf(solutionFile):
    values = dict()
    for line in solutionFile:
        words = line.strip().split(" ")
        if words[0] == "v":
            for lit in words[1:]:
                lit = int(lit)
                if lit == 0:
                    continue
                values[str(abs(lit))] = (True if lit > 0 else False)
    return values


def main():

    parser = argparse.ArgumentParser()

    parser.add_argument("--format", "-f", choices=["cnf", "opb"], default="opb")

    subparsers = parser.add_subparsers(dest='what')
    solutionParser = subparsers.add_parser("solution")
    solutionParser.add_argument("solutionFile", type=argparse.FileType("rt"),
        default = "sol.txt")
    solutionParser.add_argument("outputPreImage", type=argparse.FileType("wb"),
        default = "result_file.txt",
        nargs = "?")

    solveParser = subparsers.add_parser("solve")
    solveParser.add_argument("outputFormula", type=argparse.FileType("wt"))
    solveParser.add_argument("fileToHash", type=argparse.FileType("rb"), nargs = "?")
    solveParser.add_argument("--messageBitLength", type=int, default=55*8)
    solveParser.add_argument("--fixedInBits", type=int)
    solveParser.add_argument("--fixedInBitsStart", type=int)

    computeParser = subparsers.add_parser("compute")
    computeParser.add_argument("fileToHash", type=argparse.FileType("rb"))

    args = parser.parse_args()


    if args.what == "compute":
        data = bytearray(args.fileToHash.read())
        bt = TrueBits(data)
        h = process(bt)
        result = join(h)
        print(hex(result))

    if args.what == "solve":
        # 55 is maximum for one chunk
        msg_bytes = 54
        rnd = random.getrandbits(msg_bytes * 8)
        data = bytearray(rnd.to_bytes(msg_bytes, byteorder = 'big'))

        data = prepare(data)
        assert(len(data) * 8 % 512 == 0)

        num_chunks = len(data) * 8 // 512
        print("number of chunks:", num_chunks)

        formula = None
        if args.format == "cnf":
            formula = CNFFormula(args.outputFormula)
            bt = CNFBits(formula, num_chunks)
        elif args.format == "opb":
            formula = OPBFormula(args.outputFormula)
            bt = PBBits(formula, num_chunks)

        inBits  = bt.getInBits()
        outs = process(bt)
        outBits = list()
        for o in outs:
            outBits.extend(o)

        allBits = len(data) * 8
        forcedBits = allBits - msg_bytes * 8
        freeBits = allBits - forcedBits
        freeBits = 10
        bits = allBits - freeBits
        assert(bits >= forcedBits)

        # let us also reduce the fredom to make it easier?
        # bits += 512 - bits
        bt.setVars(int.from_bytes(data, byteorder = 'big'), inBits[-bits:])

        outZeroBits = 4
        bt.setVars(0, outBits[:outZeroBits])

        formula.writeHeader()


    if args.what == "solution":
        if args.format == "cnf":
            solution = readSolutionCnf(args.solutionFile)
        elif args.format == "opb":
            solution = readSolution(args.solutionFile)

        num_chunks = 1
        print("number of chunks:", num_chunks)

        if args.format == "cnf":
            bt = CNFBits(CNFFormula(None), num_chunks)
        elif args.format == "opb":
            bt = PBBits(OPBFormula(None), num_chunks)

        inBits  = bt.getInBits()
        outs = process(bt)

        indata = 0
        for bit in inBits:
            indata <<= 1
            indata |= solution[bit]

        nBits = len(inBits)
        message_length = indata % (2**64)
        assert(message_length % 8 == 0)
        inbytes = (indata >> (nBits - message_length)).to_bytes(message_length // 8, byteorder = 'big')

        if args.outputPreImage:
            args.outputPreImage.write(inbytes)

        outBits = list()
        for o in outs:
            outBits.extend(o)

        result = 0
        nZero = 0
        isZero = True
        for bit in outBits:
            result <<= 1
            result |= solution[bit]
            if isZero and not solution[bit]:
                nZero += 1
            else:
                isZero = False

        print("leading zeros:", nZero)
        print("pb hash value:")
        print("%040x" % (result))




if __name__ == '__main__':
    main()