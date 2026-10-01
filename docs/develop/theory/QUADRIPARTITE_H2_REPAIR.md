# Four-cube degree-two repair budget

Let `Cube = Bool^4` and let `Face = Fin 4 x Bool^3` index the actual
triangular faces of the boundary of the four-dimensional cross-polytope.  A
binary triangular cochain is `F : Face -> ZMod 2`; its tetrahedral defect is
`d2 F b`, the sum of the four incident triangle values.  The support weight
counts nonzero triangular faces.

For a finite set `S : Finset Cube`, a pairing is a partition of `S` into
unordered two-element subsets.  Its cost is the sum of the four-coordinate
Hamming distances of the paired vertices; the empty pairing has cost zero.

**Theorem (four-cube H2 repair budget).** For every binary triangular cochain
`F` and every natural budget `k`, there is an edge cochain `e` with
`weight (F + d1 e) <= k` if and only if the defect set
`{b | d2 F b != 0}` has a pairing whose total Hamming cost is at most `k`.

The necessary direction is witnessed by a cost-preserving decomposition of an
arbitrary dual cube edge set into terminal-to-terminal paths and discarded even
cycles.  The converse routes each paired terminal pair along a coordinate
geodesic.  The empty syndrome is included.  The four-face antipodal path gives
the lower boundary and reuses the existing octahedral sharpness theorem.

Primary sources: Edmonds--Johnson (1973), Section 3, pp. 90--93, for the
shortest-path parity repair mechanism; Dotterrer--Kahle, arXiv:1012.5316v2,
Definitions 2.6 and 2.8 and Proposition 5.5, for the support-count setting
and the coefficient-two upper bound.
