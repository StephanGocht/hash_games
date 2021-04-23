# Hash Games
Problem generator for different hash functions clausal encodings in CNF and pseudo-Boolean encodings in OPB.

Currently only mining games are supported, where the goal is to find a certain
number of bits in the message (pre-image) such that the computed hash digest has
a certain number of leading zeros. These instances are motivated by
Bitcoin mining where the goal is manipulate certain positions in the
Block header such that the resulting hash digest is as small as
possible (and hence has many leading zeros).

Use

```
  python3 hash_games.py --help
  python3 hash_games.py md5 mining --help
  python3 hash_games.py md5 solution --help
  python3 hash_games.py md5 compute --help
``` 
 
 
for more information.

## Acknowledgments

The adder encoding for CNF uses the same approach as

Vegard Nossum. “Instance generator for encoding preimage,second-preimage,
and collision attacks on SHA-1”. In: Proceedings of SAT Competition
2013: Solver and Benchmark Descriptions (2013), pp. 19–20.

https://github.com/vegard/sha1-sat

and the data files were generated with its halfadder generator (mkhalfadder.cc) and espresso ( https://github.com/classabbyamp/espresso-logic.git ).
