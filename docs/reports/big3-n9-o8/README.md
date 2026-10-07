# A closed Big-3 witness on S9

`hamilton-n9-word.txt` contains 362,880 generators. Starting at
`(1,2,3,4,5,6,7,8,9)`, interpret `a,b,c` as reversal of prefixes of lengths
`9,8,7`. Every permutation occurs once before the final `a` returns to the
identity. The word SHA256, excluding its final newline, is
`a1c6d5d80329b5666b79b839487b8224ca874a7c52103ad3d92ac7e260bf2475`.

Run from the repository root:

```sh
python3 docs/reports/big3-n9-o8/verify.py
```

The reader first verifies the word using literal prefix reversals and tuple
uniqueness. It then independently rebuilds the complete factor from the
2,212 whole E suppliers and 372 T representatives in `factor.json`, checks
supplier disjointness, symmetric degree two, and every word edge. No producer
imports, solver, saved adjacency, or saved permutation IDs are used.

Reverting the single O8 rejoin gives exactly two circuits of lengths 922 and
361,958. Cutting the four old O8 edges produces four exhaustive disjoint paths
with endpoint pairs `15,24,36,07` and lengths `752,152,15,361957`. Inserting
`01,23,45,67` gives the unique endpoint trace `0,7,6,3,2,4,5,1,0`. The mathematical
conditional rejoin and its supplier expansion are in
[§33 of the theory volume](../../develop/theory/BIG3_TWO_A_CUT_REPAIR.md).

The producer constructed a full factor by structured lifts of a mixed n5 base
and local repairs. Root reconstructed the complete repaired n9 factor; a
separate agent independently reconstructed 924 vertices for the local endpoint
proof and verified the complete standalone word without producer imports. The
agents belong to the same Codex model family; this is implementation independence,
not model diversity.

The repair restores two E suppliers reserved by the removed T. Their two common
D neighbours form an H four-cycle, so the H-forest recursion does not apply to
this output. This is finite native evidence, with no Lean/kernel verification,
official acceptance, unique credit, or proof for every n.

Literature check: Blanco et al., *Generating the symmetric group by three prefix
reversals*, arXiv:2511.16959v3 (22 September 2026), §4.2 Statement 2, reports
Big-3 Hamiltonicity for n=4,5,6,7,8 and retains the all-n conjecture attributed
to Sawada and Williams (2016). The v3 text was read on 6 October 2026. This
limited check does not establish that the n9 witness is new in the literature.
