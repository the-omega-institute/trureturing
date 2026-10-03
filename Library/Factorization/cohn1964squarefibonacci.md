---
bibkey: cohn1964squarefibonacci
authors: J. H. E. Cohn
year: 1964
title: "Square Fibonacci Numbers, Etc."
doi: null
url: https://www.fq.math.ca/Scanned/2-2/cohn2.pdf
claim: "Theorems 1 and 2 classify Lucas squares and twice squares at every natural index: the exceptional index sets are {1,3} and {0,6}."
strata_touched:
  - D5/S3/Arith/Primes/LucasSquareClassification
license: citation-only
triage: anchor
---

# Lucas square and twice-square classifications

J. H. E. Cohn, *Square Fibonacci Numbers, Etc.*, Fibonacci Quarterly
2(2) (1964), 109–113. The original primary paper gives the complete
Lucas square classification in Theorem 1 and the complete twice-square
classification in Theorem 2. The Lucas normalization is L_0 = 2,
L_1 = 1, L_(n+2) = L_(n+1) + L_n.

For every natural n, L_n is an integer square exactly for n = 1 or 3;
L_n equals twice an integer square exactly for n = 0 or 6. The four
exceptional values are 1, 4, 2 and 18, respectively.

The proof uses the signed Lucas trace identity, dyadic Lucas moduli
equal to three modulo four, and quadratic nonresidues detected by
Jacobi symbols. In the twice-square case, the modulus attached to
the residue minus thirty-six is coprime to three. The arithmetic
includes index zero explicitly.

## Classical argument

The exceptional values are $L_0=2$, $L_1=1$, $L_3=4$, and
$L_6=18$. For the exclusion argument, extend the trace to signed
indices by $L_{-u}=(-1)^uL_u$. Trace and norm in the golden ring give

$$
L_{j+2k}+(-1)^kL_j=L_kL_{j+k}
\qquad(j\in\mathbb Z,\ k\in\mathbb N).
$$

If $k$ is even and $s$ is positive and odd, repeated reduction gives
$L_{j+2ks}\equiv-L_j\pmod{L_k}$. Lucas doubling gives
$L_{2^{r+1}}\equiv3\pmod4$ for every $r\geq0$.

Every positive even index $n=2m$ is excluded from the square case by
$L_{2m}=L_m^2-2(-1)^m$: its residue modulo four is two or three.
For odd $n$ outside $\{1,3\}$, write $n=j+4t$ with
$j\in\{1,3\}$ and $t>0$. Factor $t=2^rs$ with $s$ odd, and put
$k=2^{r+1}$. The preceding congruence makes $L_n$ congruent to
$-1$ or $-4$ modulo the positive odd integer $L_k\equiv3\pmod4$.
Both residues have Jacobi symbol minus one, so neither is a square.

For the twice-square case, Lucas parity gives $L_n$ even exactly when
$3\mid n$. At an odd multiple of three, the Lucas recurrence modulo
eight gives $L_n\equiv4\pmod8$, which is incompatible with $2x^2$.
For $n=4t>0$, the same dyadic factorization with $j=0$ makes
$2L_n\equiv-4\pmod{L_k}$. For $n=6+8t$ with $t>0$, use $j=6$
and $k=2^{v_2(t)+2}$ to obtain $2L_n\equiv-36\pmod{L_k}$.
For $n=2+8t$, use $j=-6$ and factor $t+1$ instead. In the latter
two cases, $k$ is divisible by four and Lucas doubling modulo three
gives $3\nmid L_k$. Hence the Jacobi symbol of $-36$ is minus one.
Since $2L_n=4x^2$ would itself be a square, these congruences exclude
all the remaining indices.

The repository formalization is `lucas_square_classifications` in
`D5/S3/Arith/Primes/LucasSquareClassification.lean`. The general Fibonacci
and Lucas square-class theorems additionally need product exclusions at
distinct indices, as proved in Ribenboim, *Square Classes of Fibonacci
and Lucas Numbers*, Portugaliae Mathematica 46 (1989), 159–175.

Only the bibliographic citation and a paraphrase of the mathematical
result are retained; the paper's PDF is an external source.
