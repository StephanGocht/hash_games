import sys
import io

import math
import random

import itertools
import argparse

class BitVec(object):
    def __init__(self, numBits):
        pass


def nextInt32(it, byteorder):
    result = []
    for i in range(4):
        result.append(next(it))
    return int.from_bytes(result, byteorder=byteorder)

class TrueBits(object):
    def __init__(self, data):
        self.data = iter(data)

    def blocks(self, byteorder = 'big'):
        while True:
            w = []
            for i in range(16):
                try:
                    w.append(nextInt32(self.data, byteorder))
                except StopIteration:
                    return
            yield w

    def leftrotate(self, n, value):
        assert(value > 0)
        mask32bit = 0xFFFFFFFF
        return (n << value | n >> (32 - value)) & mask32bit

    def rightrotate(self, n, value):
        mask32bit = 0xFFFFFFFF
        return (n >> value | n << (32 - value)) & mask32bit

    def rightshift(self, n, value):
        return n >> value

    def bitwise_if(self, b,c,d):
        return (b & c) | ((~b) & d)

    def bitwise_xor(self, *args):
        result = 0
        for i in args:
            result ^= i
        return result

    def bitwise_md5_i(self, b, c, d):
        return c ^ (b | ~d)

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

    def rightrotate(self, n, value):
        return n[:value] + n[value:]

    def rightshift(self, n, value):
        return ([self.zero] * value) + n[:value]

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

        self.zero = self.constant(0,1)

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

    def rightrotate(self, n, value):
        return n[:value] + n[value:]

    def rightshift(self, n, value):
        return ([self.zero] * value) + n[:value]

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

def sha256(bt):

    k = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b,
        0x59f111f1, 0x923f82a4, 0xab1c5ed5, 0xd807aa98, 0x12835b01,
        0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7,
        0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
        0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152,
        0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147,
        0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
        0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819,
        0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116, 0x1e376c08,
        0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f,
        0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
        0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2 ]
    k = [bt.constant(x, 32) for x in k]

    s = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f,
        0x9b05688c, 0x1f83d9ab, 0x5be0cd19 ]
    s = [bt.constant(x, 32) for x in s]


    for w in bt.blocks():
        w = list(w)
        for i in range(16, 64):
            s0 = bt.bitwise_xor(bt.rightrotate(w[i-15],  7), bt.rightrotate(w[i-15], 18), bt.rightshift(w[i-15],  3))
            s1 = bt.bitwise_xor(bt.rightrotate(w[i- 2], 17), bt.rightrotate(w[i- 2], 19), bt.rightshift(w[i- 2], 10))
            w.append(bt.bitsum32(w[i-16], s0, w[i-7], s1))

        a = s[0]
        b = s[1]
        c = s[2]
        d = s[3]
        e = s[4]
        f = s[5]
        g = s[6]
        h = s[7]

        for i in range(0, 64):
            S1 = bt.bitwise_xor(bt.rightrotate(e, 6), bt.rightrotate(e, 11), bt.rightrotate(e, 25))
            ch = bt.bitwise_if(e, f, g)
            temp1 = bt.bitsum32(h, S1, ch, k[i], w[i])
            S0 = bt.bitwise_xor(bt.rightrotate(a, 2), bt.rightrotate(a, 13), bt.rightrotate(a, 22))
            maj = bt.bitwise_mayority(a, b, c)
            temp2 = bt.bitsum32(S0, maj)

            h = g
            g = f
            f = e
            e = bt.bitsum32(d, temp1)
            d = c
            c = b
            b = a
            a = bt.bitsum32(temp1, temp2)

        s[0] = bt.bitsum32(s[0], a)
        s[1] = bt.bitsum32(s[1], b)
        s[2] = bt.bitsum32(s[2], c)
        s[3] = bt.bitsum32(s[3], d)
        s[4] = bt.bitsum32(s[4], e)
        s[5] = bt.bitsum32(s[5], f)
        s[6] = bt.bitsum32(s[6], g)
        s[7] = bt.bitsum32(s[7], h)

    return s


def sha1(bt):
    h = [
            bt.constant(0x67452301, 32),
            bt.constant(0xEFCDAB89, 32),
            bt.constant(0x98BADCFE, 32),
            bt.constant(0x10325476, 32),
            bt.constant(0xC3D2E1F0, 32),
        ]

    kall = [
        bt.constant(0x5A827999, 32),
        bt.constant(0x6ED9EBA1, 32),
        bt.constant(0x8F1BBCDC, 32),
        bt.constant(0xCA62C1D6, 32),
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

def md4(bt):
    h = [0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476]
    h = [bt.constant(x, 32) for x in h]

    k = [0x5A827999, 0x6ED9EBA1]
    k = [bt.constant(x, 32) for x in k]

    abcd_idx = lambda i,j: (j-i) % 4

    for w in bt.blocks(byteorder = 'little'):
        w = list(w)

        h0 = h[0]
        h1 = h[1]
        h2 = h[2]
        h3 = h[3]

        ki = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
        s = [3,7,11,19] * 4
        for i in range(16):
            a,b,c,d = (h[abcd_idx(i,j)] for j in range(4))
            tmp = bt.bitsum32(a, bt.bitwise_if(b,c,d), w[ki[i]])
            h[abcd_idx(i,0)] = bt.leftrotate(tmp, s[i])

        ki = [0, 4, 8, 12, 1, 5, 9, 13, 2, 6, 10, 14, 3, 7, 11, 15]
        s = [3,5,9,13] * 4
        for i in range(16):
            a,b,c,d = (h[abcd_idx(i,j)] for j in range(4))
            tmp = bt.bitsum32(a, bt.bitwise_mayority(b,c,d), w[ki[i]], k[0])
            h[abcd_idx(i,0)] = bt.leftrotate(tmp, s[i])

        ki = [0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15]
        s = [3,9,11,15] * 4
        for i in range(16):
            a,b,c,d = (h[abcd_idx(i,j)] for j in range(4))
            tmp = bt.bitsum32(a, bt.bitwise_xor(b,c,d), w[ki[i]], k[1])
            h[abcd_idx(i,0)] = bt.leftrotate(tmp, s[i])

        h[0] = bt.bitsum32(h[0], h0)
        h[1] = bt.bitsum32(h[1], h1)
        h[2] = bt.bitsum32(h[2], h2)
        h[3] = bt.bitsum32(h[3], h3)

    return h

def md5(bt):
    h = [0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476]
    h = [bt.constant(x, 32) for x in h]

    k = [int(abs(math.sin(i+1)) * 2**32) & 0xFFFFFFFF for i in range(64)]
    k = [bt.constant(x, 32) for x in k]

    s = [7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22,
         5,  9, 14, 20, 5,  9, 14, 20, 5,  9, 14, 20, 5,  9, 14, 20,
         4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23,
         6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21]

    f = [ lambda b, c, d: bt.bitwise_if(b,c,d),
          lambda b, c, d: bt.bitwise_if(d,b,c),
          lambda b, c, d: bt.bitwise_xor(b,c,d),
          lambda b, c, d: bt.bitwise_md5_i(b,c,d) ]

    ki = [i for i in range(16)] + \
         [(5*i + 1)%16 for i in range(16)] + \
         [(3*i + 5)%16 for i in range(16)] + \
         [(7*i)%16 for i in range(16)]

    abcd_idx = lambda i,j: (j-i) % 4

    for w in bt.blocks(byteorder = 'little'):
        w = list(w)

        h0 = h[0]
        h1 = h[1]
        h2 = h[2]
        h3 = h[3]

        e = 0
        for r in range(4):
            for i in range(16):
                a,b,c,d = (h[abcd_idx(i,j)] for j in range(4))
                tmp = bt.bitsum32(a, f[r](b,c,d), w[ki[e]], k[e])
                tmp = bt.leftrotate(tmp, s[e])
                h[abcd_idx(i,0)] = bt.bitsum32(tmp, b)
                e += 1

        h[0] = bt.bitsum32(h[0], h0)
        h[1] = bt.bitsum32(h[1], h1)
        h[2] = bt.bitsum32(h[2], h2)
        h[3] = bt.bitsum32(h[3], h3)

    return h


def prepare(data, byteorder = 'big'):
    message_length = len(data) * 8

    data.append(0x80)

    bytes_per_block = (512 // 8)
    used_bytes = message_length//8 + 1 + 8
    to_add = (bytes_per_block - used_bytes) % bytes_per_block

    data.extend([0] * to_add)
    data.extend(message_length.to_bytes(8, byteorder = byteorder))
    assert(len(data) % bytes_per_block == 0)

    return data

def join(h, byteorder = 'big'):
    result = 0
    for x in h:
        for byte in x.to_bytes(32 // 8, byteorder = byteorder):
            result = result << 8 | byte
    return result

def readSolutionOpb(solutionFile):
    values = dict()
    for line in solutionFile:
        words = line.strip().split(" ")
        if words[0] == "v":
            for i, lit in enumerate(words[1:]):
                value = True
                if lit[0] == "-" or lit[0] == "~":
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

def renderSolution(bt, solution, outputPreImage):
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

    if outputPreImage:
        outputPreImage.write(inbytes)

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

def main():

    parser = argparse.ArgumentParser()

    parser.add_argument("hash_function", choices = ["sha1","sha256","md4","md5"])

    parser.add_argument("--format", "-f", choices=["cnf", "opb"], default="opb")
    parser.add_argument("--seed", type=int)

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
    solveParser.add_argument("--messageBytes", type=int, default=55)
    solveParser.add_argument("--fixedInBits", type=int)
    solveParser.add_argument("--fixedInBitsStart", type=int)

    solveParser = subparsers.add_parser("analyze")
    solveParser.add_argument("outputFormula", type=argparse.FileType("wt"))
    solveParser.add_argument("fileToHash", type=argparse.FileType("rb"), nargs = "?")
    solveParser.add_argument("--messageBytes", type=int, default=55)

    computeParser = subparsers.add_parser("compute")
    computeParser.add_argument("fileToHash", type=argparse.FileType("rb"))

    args = parser.parse_args()

    if args.seed:
        random.seed(args.seed)
    random.seed(1)

    if args.hash_function == "sha1":
        process = sha1
        byteorder = 'big'
    elif args.hash_function == "sha256":
        process = sha256
        byteorder = 'big'
    elif args.hash_function == "md4":
        process = md4
        byteorder = 'little'
    elif args.hash_function == "md5":
        process = md5
        byteorder = 'little'

    if args.what == "compute":
        data = bytearray(args.fileToHash.read())
        data = prepare(data, byteorder)
        bt = TrueBits(data)
        h = process(bt)
        result = join(h, byteorder)
        print(hex(result))

    if args.what == "solve":
        if args.fileToHash:
            data = bytearray(args.fileToHash.read())
            msg_bytes = len(data)
        else:
            # 55 is maximum for one chunk
            msg_bytes = args.messageBytes
            rnd = random.getrandbits(msg_bytes * 8)
            data = bytearray(rnd.to_bytes(msg_bytes, byteorder = 'big'))

        data = prepare(data)
        assert(len(data) * 8 % 512 == 0)

        num_chunks = len(data) * 8 // 512
        print("number of chunks:", num_chunks)

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
        # forcedBits at the end of the message contain padding and the
        # length of the message
        forcedBits = allBits - msg_bytes * 8
        # maximum number of free bits
        maxFreeBits = allBits - forcedBits
        # actual number of free bits
        freeBits = 10
        bits = allBits - freeBits
        assert(bits >= forcedBits)

        bt.setVars(int.from_bytes(data, byteorder = 'big'), inBits[-bits:])

        outZeroBits = 4
        bt.setVars(0, outBits[:outZeroBits])

        formula.writeHeader()

    if args.what == "analyze":
        if args.fileToHash:
            data = bytearray(args.fileToHash.read())
            msg_bytes = len(data)
        else:
            # 55 is maximum for one chunk
            msg_bytes = args.messageBytes
            rnd = random.getrandbits(msg_bytes * 8)
            data = bytearray(rnd.to_bytes(msg_bytes, byteorder = 'big'))

        data = prepare(data)
        assert(len(data) * 8 % 512 == 0)

        num_chunks = len(data) * 8 // 512
        print("number of chunks:", num_chunks)

        if args.format == "cnf":
            formula = CNFFormula(args.outputFormula)
            bt1 = CNFBits(formula, num_chunks)
            bt2 = CNFBits(formula, num_chunks)
        elif args.format == "opb":
            formula = OPBFormula(args.outputFormula)
            bt1 = PBBits(formula, num_chunks)
            bt2 = PBBits(formula, num_chunks)

        inBits1  = bt1.getInBits()
        outs = process(bt1)
        outBits1 = list()
        for o in outs:
            outBits1.extend(o)

        inBits2  = bt2.getInBits()
        outs = process(bt2)
        outBits2 = list()
        for o in outs:
            outBits2.extend(o)

        inBitsDiff  = bt1.bitwise_xor(inBits1, inBits2)
        outBitsDiff = bt1.bitwise_xor(outBits1, outBits2)


        freeInBits  = 2
        diffOutBits = 1
        bt1.setVars(int.from_bytes(data, byteorder = 'big'), inBits1[freeInBits:])
        for diffBit in inBitsDiff[freeInBits:]:
            formula.print("1 ~%s >= 1 ;"%(diffBit))

        for diffBit in outBitsDiff[:diffOutBits]:
            formula.print("1 %s >= 1 ;"%(diffBit))


        formula.writeHeader()

    if args.what == "solution":
        if args.format == "cnf":
            solution = readSolutionCnf(args.solutionFile)
        elif args.format == "opb":
            solution = readSolutionOpb(args.solutionFile)

        num_chunks = 1
        print("number of chunks:", num_chunks)

        if args.format == "cnf":
            bt = CNFBits(CNFFormula(None), num_chunks)
        elif args.format == "opb":
            bt = PBBits(OPBFormula(None), num_chunks)


        renderSolution(bt, solution, args.outputPreImage)




if __name__ == '__main__':
    main()