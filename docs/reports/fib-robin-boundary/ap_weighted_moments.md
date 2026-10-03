# Finite weighted moments on actual arithmetic progressions

`ap_weighted_moments.py` uses Python 3.9+ and only the standard library:

```sh
python3 ap_weighted_moments.py --out '/tmp/ap weighted results.json'
```

The required output path is the only result file written. The program rejects
optimized execution and source overwrite, including symbolic and hard links.
It works from another working directory and accepts spaces in paths. The JSON
binds the deterministic results to the program's SHA-256. It contains no
floating-point numbers, elapsed times, timestamps or unverified Robin budgets.

For positive integers V and g in a specified interval I=[G0,G1], the program
uses the actual integer N=1+gV, T=|I| and X=1+VG1. The observed moment is the
sum M=sum_g Z(N)^k, not the average; dividing by T gives the uniform-g mean.
Here Z(N)=sum_{d|N}1/d=sigma(N)/N and k is 1, 2 or 3.

The exact multiplicative coefficients satisfy b_k(1)=1 and

`b_k(p^a) = Z(p^a)^k - Z(p^(a-1))^k`.

They are stored internally as integer numerators with denominator d^k. For
example b_2(2)=5/4 and b_2(4)=13/16; b_3(2)=19/8 and b_3(4)=127/64.
Local representatives for p=2,3,5 and a=1,2,3 are retained. The complete finite
coefficient table verifies b_1(d)=1/d.

The program independently lists actual divisors by trial division, obtains
their reciprocal sum through the exact divisor-pair identity, and verifies

`M = sum_{d<=X} b_k(d)*A_I(d)`

exactly using the common denominator lcm(N_g)^k. A_I(d) is counted from the
actual divisor incidences and compared with the unique-residue floor formula;
noncoprime moduli have zero hits. A separate ordered-divisor convolution groups
terms by their common lcm for N=2,4,6,9,12,27,49,91,121. Its coefficients agree
with b_k and its total agrees with the direct Z(N)^k. These representatives
cover primes, repeated prime powers and multiple distinct primes. They provide
an independent relation check without repeating the earlier large tuple test.

The finite normalization is explicitly

`U_X = sum_{d<=X} b_k(d)/d`,

with all d included. It is **not an infinite U**. The probability weight on
divisors is mu_X(d)=(b_k(d)/d)/U_X. This divisor-weight law is different from
the uniform law on multipliers g. With K(d)=d*A_I(d)/X, the exact bridge is

`E_mu_X[K] = M/(X*U_X)`.

The JSON also reports the coprime mass U_(V,X)/U_X, where U_(V,X) restricts
the sum to gcd(d,V)=1. The centered identity therefore uses an indicator:

`B_X/(X*U_X) = E_mu_X[K-(T/X)*1_(gcd(d,V)=1)]`.

For D among the distinct valid integers in
`{1,T,V,isqrt(X),X//4,X//2,X}`, each record reports the finite probability mass,
actual moment contribution and signed boundary on both sides. Probability
masses for K in `[0,1/4)`, `[1/4,1/2)`, `[1/2,3/4)`, `[3/4,1)` and `{1}`
are retained, together with extreme individual signed contributions. These
are weighted actual joint counts, not products of marginal probabilities.

The small range is V=1,...,12, G0=1,...,6 and T=1,...,6: 432 complete
intervals with X<=133. It includes small composite V, single-element intervals,
and divisors larger than T that hit once or miss. Five representative intervals,
per-order extrema, sign counts and a hash of all computed summaries are kept;
per-divisor arrays and every intermediate object are not dumped.

The signed finite boundary is B_X=M-T*U_(V,X). Its observed signs are:

| Order k | Positive B_X | Negative B_X |
|---|---|---|
| 1 | 259 | 173 |
| 2 | 258 | 174 |
| 3 | 255 | 177 |

There is no zero-mean assumption. For all three orders, the largest B_X in
this range occurs at V=7, G0=5, T=1, and the smallest at V=7, G0=6, T=5.
The JSON retains exact rational values. Some D splits have opposite signs on
the two sides: 266 intervals for k=1, 255 for k=2 and 251 for k=3.

These signs concern the finite boundary. For the convergent coefficient series,
the infinite boundary is

`B_infinite = B_X - T*sum_{d>X,gcd(d,V)=1} b_k(d)/d`.

The omitted tail is nonnegative. Thus B_X>0 alone does not imply
B_infinite>0; a negative B_X is an upper bound for B_infinite. The program
reports an infinite-boundary sign only for k=1, using the elementary tail
estimate

`0 <= T*sum_{d>X,gcd(d,V)=1} 1/d^2 <= T/X`.

This gives the rational enclosure `[B_X-T/X,B_X]`, enlarged by any recorded
finite arithmetic enclosure error. Its sign is reported only when the whole
interval is strictly positive or strictly negative; otherwise it is `unknown`.
Among the 432 small intervals this certifies 152 positive signs and 173 negative
signs, leaving 107 unknown. In particular 107 of the 259 positive finite
boundaries do not receive a positive infinite-boundary certificate from this
bound. No corresponding infinite sign is reported for k=2 or k=3.

Four additional cases use the complete genuine Fibonacci-source intervals
`ceil(F_r/10)<=g<=floor(F_r/5)`. All 193 actual sources are independently
reconstructed and greedy-decoded to check their composition and unit bit one.

| Prime index r | V=F_r | Multipliers g | X | Finite B_X signs, k=1,2,3 |
|---|---|---|---|---|
| 7 | 13 | 2..2 | 27 | negative |
| 11 | 89 | 9..17 | 1,514 | negative |
| 13 | 233 | 24..46 | 10,719 | negative |
| 17 | 1,597 | 160..319 | 509,444 | positive |

The k=1 infinite-boundary intervals also have those respective signs. Simple
outward rational enclosures derived from the retained data are `[-157/1000,
-119/1000]`, `[-28/1000,-22/1000]`, `[-340/1000,-337/1000]` and
`[79/1000,80/1000]`. These concern the signed boundary, not a Robin margin.

Every moment identity is checked exactly before serialization. To avoid adding
all unrelated large denominators, each term of U_X and B_X is rounded outward
to the fixed grid with denominator 10^24 using integer quotient and remainder.
The sum of at most X such terms has interval width at most X/10^24. Small-range
B_X is additionally computed as one exact rational; the larger cases retain
rigorous rational enclosures. Ratios and D-tail differences propagate the
endpoint bounds, and their actual widths are included. Empty D=X tails are
recorded as exact zero. No floating-point or elapsed-time input affects output.

The data supply actual finite signatures and an enumeration baseline for
weighted-moment and boundary interfaces. Apart from the explicitly proved
k=1 tail enclosure, they do not establish infinite coefficient bounds,
asymptotic moments, zero-mean boundary behavior, logarithmic budgets, or RH.
