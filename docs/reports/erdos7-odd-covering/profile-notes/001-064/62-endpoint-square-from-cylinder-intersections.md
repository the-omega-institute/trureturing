[Index](../../marked_head_profile.md) · [Common deleted measure](57-common-deleted-measure-coupling.md) · [Endpoint cylinder caps](59-endpoint-linear-source-deletion-bound.md) · [Tensor reference](61-exact-tensor-numerator-reference.md)

# A uniform endpoint square bound from original-cylinder intersections

For all actual finite original-label families approaching source
vertex404, survivor mass S=D=3/20, and shallow carrier mixture(0,1),
every independently labelled complete original357 test A satisfies

    limsup integral_survivor A^2<=4559/900.             (1)

In particular the current signed square barrier45 gives

    liminf [45*S-integral_survivor A^2]>=379/225.

This strictly improves the old square margin5701/3888 by
21203/97200. The proof rebuilds the entire square numerator from
the actual surviving-cylinder bounds in profile59. It does not
subtract a new block from an old bound with already spent deletion
credits. The result is uniform over independently chosen original
test residues, including residues that change along the sequence.

This is an ordinary mathematical endpoint theorem, with complete
exponent tails. It is not a quantitative neighborhood estimate,
a replacement for the global K consumer, or a Lean result.

## 1. Original labelled intersections control every integer moment

For nonnegative exponents a,b,e let C_(a,b,e) be the chosen test
cylinder of modulus3^a*5^b*7^e. The unit label C_(0,0,0) is the
whole space. A complete original test is

    A=sum_(a,b,e>=0)1_(C_(a,b,e)).

There is only one cylinder at each original modulus. Missing labels
can be added to bound a partial test, since all terms and the square
are nonnegative and increasing.

For any two such original labels, their intersection is empty or
one cylinder at the least common multiple of their moduli. In
exponent coordinates the latter is the componentwise maximum. No
common residue, product form, or nesting between test labels is
assumed. If c_(a,b,e) is a uniform bound on the actual surviving
mass of every cylinder with that modulus, then

    integral_survivor A^2
      <=sum_(a,b,e>=0)(2a+1)*(2b+1)*(2e+1)*c_(a,b,e). (2)

Indeed the number of ordered exponent pairs with maximum a is
(a+1)^2-a^2=2a+1. The choices at the three primes multiply, and
every compatible pair intersection is bounded by the cap for its
own maximum exponent triple. Incompatible pairs contribute zero.
Prove this first for finite exponent boxes and then use monotone
convergence. The unit-unit pair occurs exactly once; its mass is
the actual S.

More generally, the same argument gives the r-th power bound with
factors(a+1)^r-a^r at each prime for every positive integer r.
The count is over ordered original-label r-tuples; the common
intersection is again empty or an lcm cylinder. We use r=2 below.
The different cylinder caps need not be jointly attainable for
this upper-bound argument.

## 2. Complete source and survivor cap tables

Use the exact endpoint setting and arbitrary-cylinder bounds proved
in profile59. Let B_(a,b) denote a bound on raw35 source mass and
C_(a,b) a bound on the actual surviving old-coordinate marginal.
The tables are

| Old35 modulus | B: raw source cap | C: surviving marginal cap |
| --- | ---: | ---: |
| 1 | 1/4 | 3/20 |
| 3 | 1/8 | 11/120 |
| 9 | 1/12 | 2/45 |
| 3^a, a>=3 | (3/4)*3^(-a) | (11/20)*3^(-a) |
| 5 | 1/10 | 1/18 |
| 5^b, b>=2 | (1/2)*5^(-b) | (4/9)*5^(-b) |
| 15 | 1/15 | 1/25 |
| 3*5^b, b>=2 | (1/3)*5^(-b) | same as B |
| 9*5^b, b>=1 | (1/9)*5^(-b) | same as B |
| 3^a*5^b, a>=3,b>=1 | 3^(-a)*5^(-b) | same as B |

The caps C come from the same actual deleted measure. At the
endpoint all cofactor budgets are saturated, so actual deletion
equals the virtual original-cofactor measure. Its root0, cell1,
source-free first-five slot, and root1 times that slot contributions
yield the four shallow improvements. Its complete source-free
five-coordinate cofactors also yield the improved deep pure3 tail.
The weighted root0 and cell1 source caps yield the deep pure5 tail.
Profile59 proves these statements for every original cylinder;
they are not restricted to one tensor witness.

For every positive-seven exponent e, dropping mixed-seven deletion
and retaining pure7 normalization gives

    c_(a,b,e)<=u_e*B_(a,b), u_e=6/(5*7^e).          (3)

For e=0 use C_(a,b). In(3) the seven residue can differ for every
original label. The cap applies equally to the lcm cylinder of a
compatible pair, regardless of which two residues produced it.

## 3. The exact complete square sum

Write W(n)=2n+1. The geometric sums used below are

    sum_(a>=3)W(a)*3^(-a)=4/9,
    sum_(b>=1)W(b)*5^(-b)=7/8,
    sum_(b>=2)W(b)*5^(-b)=11/40,
    sum_(e>=1)W(e)*u_e=2/3.

The complete raw35 weighted cap sum is

    sum_(a,b>=0)W(a)*W(b)*B_(a,b)
      =1/4+3/8+5/12+(3/4)*(4/9)
       +(1/2)*(7/8)+3*(1/3)*(7/8)
       +5*(1/9)*(7/8)+(4/9)*(7/8)
      =57/16.                                      (4)

Replacing B by C at zero seven subtracts exactly

| Cap improvement | Its full ordered-pair contribution |
| --- | ---: |
| Unit mass 1/4 to S=3/20 | 1/10 |
| Modulus3 | 3*(1/30)=1/10 |
| Modulus9 | 5*(7/180)=7/36 |
| Modulus5 | 3*(2/45)=2/15 |
| Modulus15 | 9*(2/75)=6/25 |
| All pure3 depths a>=3 | (1/5)*(4/9)=4/45 |
| All pure5 depths b>=2 | (1/18)*(11/40)=11/720 |

These disjoint exponent categories give total loss3139/3600.
Hence the complete zero-seven square contribution is at most

    57/16-3139/3600=4843/1800.

The positive-seven pair contribution from(3) is at most

    (2/3)*(57/16)=19/8.

Substitution in(2) proves the absolute full-square bound

    integral_survivor A^2<=4843/1800+19/8=4559/900.  (5)

Consequently

    45*(3/20)-4559/900=379/225,
    379/225-5701/3888=21203/97200>0.                (6)

The multiplier9 at modulus15 counts nine different ordered pairs
whose exponent maximum is(1,1,0). Each is an occurrence in the
actual square expansion. Applying the same cylinder cap to these
nine terms is valid linearity of integration, not nine deductions
from a previously paid source budget.

The old square margin is used only in the final comparison(6).
No part of the proof of(5) requires decomposing or strengthening
the internal payments used to prove that earlier margin.

## 4. Uniform quadratic tails and passage to the endpoint

The pointwise square can be infinite on a Haar-null set; all its
integrals and the limiting argument are controlled by complete
summable intersection caps. For every actual source family its
pure7-normalized surviving measure is bounded by6/5 times full
raw357 Haar measure. In particular a compatible original-pair
intersection with maximum exponents(a,b,e) has mass at most

    (6/5)*3^(-a)*5^(-b)*7^(-e).

Let A_N retain test labels with every exponent at most N. Expanding
the nonnegative difference A^2-A_N^2 into original ordered pairs
therefore gives the uniform tail bound

    integral(A^2-A_N^2)
       <=(6/5)*sum_(max(a,b,e)>N)
              (2a+1)*(2b+1)*(2e+1)*3^(-a)*5^(-b)*7^(-e). (7)

The right side tends to zero because each one-dimensional sum is
a polynomial times a convergent geometric series. This proves the
needed uniform approximation of the square integrals; a bare first
moment estimate would not suffice.

Now take any sequence of finite actual families with the stated
source, survivor-mass and carrier limits. The labelwise diagonal
subsequence argument in profile59 makes every fixed original source
and test label eventually constant. Geometric forbidden-union tails
give L1 convergence of the actual surviving density, and the pure7
normalizers stay at least5/6. For fixed N, the bounded finite test
A_N^2 therefore has convergent integrals. Equation(7) passes this
convergence to the complete square uniformly over the changing test
labels. Every limiting family obeys the endpoint caps and(5).
Any violation of(1) would thus produce a limiting counterexample
to(5), which is impossible.

## 5. Exact checks and what remains

[The checker](../../frontier/endpoint-bounds/endpoint_square_numerator.py) reconstructs
the endpoint caps from the pinned profile59 helper and certificate,
then independently sums the complete quadratic cap table. For
exponent boxes of heights3,5,9 it verifies that direct finite sums
plus explicit complementary geometric tails equal4559/900 exactly.
The old margin is read from the pinned actual-survival boundary
certificate, preserving the current square barrier45.

An additional independent finite check constructs the genuine
original forbidden family at height2 and its complete period11025.
It evaluates two tests with27 original labels: nested residues and
independently chosen residues. For each it checks direct integration
of A^2 against all729 ordered pair intersections, their lcm-exponent
multiplicities, empty incompatible intersections, and the actual
finite-source cylinder caps. These finite sources are not treated
as exact endpoint families and are not required to obey(5).

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/endpoint-bounds/endpoint_square_numerator.py --check
```

The [certificate](../../certificates/source_norms/endpoint-bounds/endpoint_square_numerator.json)
contains exact rational arithmetic. The script is read-only unless
`--output PATH` is supplied; its checks remain enabled under -O.
The ordinary proof carries the universal quantifiers and limits.

This improves one full nonlinear numerator cost uniformly on the
specified endpoint class. Applying the gain throughout the global
source domain still requires a compatible neighborhood estimate
and treatment of the other source/carrier cases. Neither the
current endpoint bound nor its comparison with one tensor witness
settles the unrestricted covering problem.
