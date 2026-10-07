# Native n10 Hamilton certificate

The complete `factor.json` supplies 17,951 whole E switches and 2,583 standard T switches on labels 1 through 10. The baseline consists of the `(ab)^10` D bracelets, with prefix lengths a=10, b=9, c=8. `hamilton-n10-word.txt` starts at the identity and includes its final closing edge.

This is a finite n10 result. It does not establish the all-n Hamilton theorem or a next-dimension boundary invariant.

Run from any directory, with Python 3 and no third-party packages:

```sh
python3 verifier.py
```

The verifier reads its sibling factor and word, independently reconstructs every removed a/b edge and replacement c edge, checks complete legal labels and lengths, symmetric removed/replacement matchings and distinct whole/reserved suppliers, and checks all 3,628,800 word edges against the resulting factor. A dense Lehmer-rank bitset confirms 3,628,800 distinct permutations and the actual return to the identity. The default run writes no files and also undoes the final E, directly traverses all nine exhaustive input paths, verifies their offsets and matching, recovers both input circles, and checks the unique repaired endpoint circuit. `python3 verifier.py --emit` reconstructs the word from the supplied factor and performs the same exhaustive vertex and closure checks.

The final operation adds the unused whole E supplier `(2,[1,3,10,4,7,8,9,5,6])` to an input factor with circles of lengths 3,627,382 and 1,418. Its eighteen-edge `(cb)^9` switch has nine actual outside paths recorded in `factor.json`. Their endpoint matching joins into one eighteen-endpoint circuit and covers all 10! vertices. [§37 of the canonical theory volume](../../develop/theory/BIG3_TWO_A_CUT_REPAIR.md#37-增补指定十八端点的完整供应重接) states and proves this conditional endpoint theorem with the actual closing c edge. Construction provenance also records the earlier inverse expansion of upper T2349 into its two reserved E suppliers.

The full final supplier lists are included. No earlier fixture, private local module, solver, network service, or absolute path is needed for verification.
