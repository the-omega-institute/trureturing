[Index](../../marked_head_profile.md) · [Primitive original-label moments](336-maximal-label-fourier-overlap-and-uncovered-density.md) · [Actual prefix completion](340-whole-cover-completion-constrains-original-prefix-loads.md) · [Probability transport](343-original-prefix-sat-reductions-and-transport-obstructions.md)

# Original Fourier moments and finite-probe obstructions

This is a finite diagnostic separating two necessary whole-cover tests on the **same actual conditional fibre**. It is not a new exclusion of an unbounded family, and it does not show an advantage over all tests run across all old fibres. The original family below has an explicit uncovered integer and a small global density.

## 1. General conditional moment interface, with fixed conventions

Fix a genuine old survivor `x` of all already-processed original classes and a depth-`t` prefix `J`. On the resulting finite residual cyclic group with its uniform law, let

\[
 N(z)=\mathbf1_{\text{current union}}(z)
       +\sum_{i\ \mathrm{compatible}}\mathbf1_{r_i\bmod m_i}(z),
 \qquad g=N-1.
\]

The sum retains original-label multiplicities. Whole coverage implies `g>=0`. With the convention

\[
 \widehat g(\chi)=\mathbb E[g\overline\chi],\qquad
 K_{ab}=\mathbb E[g\chi_a\overline{\chi_b}],
\]

we have

\[
 c^*Kc=\mathbb E\left[g\left|\sum_a\overline{c_a}\chi_a\right|^2\right]\ge0.
\]

Using the transposed Gram convention instead conjugates the displayed coefficients and requires the corresponding change in the quadratic-form formula; it does not change positive semidefiniteness.

For an AP `a mod d` in `Z/QZ`, `d|Q`, direct summation gives

\[
 \widehat{\mathbf1_{a\bmod d}}(\chi)
 =\begin{cases}\overline{\chi(a)}/d,&\operatorname{cond}(\chi)\mid d,\\0,&\text{otherwise}.\end{cases}
\]

Conditional on the fixed old state `x`, the prefix `J` has Haar mass `p^-t`; the diagonal is

\[
 r=\mathbb E g=p^t(a_J+F_J-p^{-t}).
\]

This requires the *actual* current intersection with `J` and the actual compatible affine pullbacks. If a nontrivial character lives only on future prime coordinates, its current-union coefficient vanishes because the current union depends only on the current-prime coordinate and the conditional law is uniform product CRT. It does not vanish merely by terminology under a different correlated conditional law. Thus the other coefficients are the explicit original-label sums over residual moduli divisible by that character's conductor.

For `u=hat g(chi)`, `v=hat g(psi)`, `w=hat g(chi bar psi)` the three-character matrix is

\[
 K=\begin{pmatrix}r&u&v\\\bar u&r&\bar w\\\bar v&w&r\end{pmatrix},
\]

so

\[
 \det K=r^3-r(|u|^2+|v|^2+|w|^2)
             +2\operatorname{Re}(\bar u v w).
\]

These identities use one synchronized Fourier convention. A determinant is one necessary test, alongside nonnegative diagonal and two-by-two minors. The complete character matrix being PSD is equivalent to `g>=0`; the useful question is what a small selected matrix detects.

## 2. A complete original family with 20 distinct odd moduli

For `0<=e<=19`, define

\[
 g_e=3^e5^{19-e},\quad r_e=3+\lfloor e/2\rfloor,\quad d_e=13g_e,
\]

and choose the unique residue `a_e mod d_e` satisfying

\[
 a_e\equiv0\pmod{g_e},\qquad a_e\equiv r_e\pmod{13}.
\]

All original moduli are distinct odd integers. They are pairwise incomparable by divisibility: increasing `e` increases the 3-exponent and decreases the 5-exponent.

There is an explicit private integer for every original label. Set

\[
 s_e=\left((r_eg_e^{-1}-1)15^{-1}\right)\bmod13,
 \qquad n_e=g_e(1+15s_e).
\]

Then `n_e mod13 = r_e`, while

\[
 v_3(n_e)=e,\qquad v_5(n_e)=19-e.
\]

Thus `n_e` belongs to its own AP. If `f>e`, `g_f` asks for a larger 3-exponent; if `f<e`, it asks for a larger 5-exponent. In either case `g_f` does not divide `n_e`, so `n_e` belongs to no other original AP. This proves irredundancy on the union without assuming whole coverage. Integer 0 is uncovered, since every `r_e` is nonzero modulo 13.

The full old period and full period are

\[
 D=3^{19}5^{19}=22168378200531005859375,
 \qquad Q=13D=288188916606903076171875.
\]

On the actual old fibre `N=0 mod D`, use the *physical CRT coordinate* `z=N mod13`. Every old cofactor divides `D`; every residue `3,...,12` has exactly two original labels. Therefore

\[
 M(z)=2\mathbf1_{\{3,\ldots,12\}}(z),\qquad
 g(z)=1-2\mathbf1_{\{0,1,2\}}(z).
\]

There is no current class in this family. The conditional reference law is uniform on all 13 residual points. The old fibre has positive full-Haar mass `1/D`.

Coordinate transport matters: if one instead parameterizes the fibre by `N=Dt`, then `D=11 mod13` and `D^-1=6 mod13`. The physical frequencies `0,1,2` become affine frequencies `0,11,9`. One must transport the phase/test along this permutation; silently treating `t` as `N mod13` would change the chosen matrix.

## 3. Every nonzero single mode passes, with an exact margin

Let `zeta=exp(2 pi i/13)`. The mean is

\[
 r=\widehat g(0)=7/13>0.
\]

For **every** nonzero frequency `k mod13`,

\[
 \widehat g(k)=-\frac2{13}(1+\zeta^{-k}+\zeta^{-2k}),\qquad
 |\widehat g(k)|\le6/13<7/13=r.
\]

This uses only the triangle inequality, so there is no unexamined frequency. Every two-character principal minor is strictly positive, with lower bound

\[
 r^2-|\widehat g(k)|^2\ge(49-36)/169=1/13.
\]

## 4. A three-character negative direction without numerical trigonometry

Use the same frequency span `0,1,2`, after a harmless diagonal phase change that centers it at the missing point 1:

\[
 h(z)=1+\zeta^{z-1}+\zeta^{2(z-1)}.
\]

Put `theta=2 pi/13`, `c=cos(theta)`, `d=cos(2 theta)`. Direct Fourier summation gives

\[
 \mathbb E[g|h|^2]=\frac{9-16c-8d}{13}.
\]

The exact angle comparisons

\[
 \theta<\pi/6,\quad 2\theta<\pi/3
\]

imply

\[
 c>\sqrt3/2>3/4,\qquad d>1/2.
\]

Consequently

\[
 \boxed{\mathbb E[g|h|^2]<-7/13<0.}
\]

There is also a pure exact determinant bound. In the centered character basis,

\[
 13K=\begin{pmatrix}7&a&b\\a&7&a\\b&a&7\end{pmatrix},
 \qquad a=-2-4c<-5,\quad b=-2-4d<-4.
\]

Hence

\[
 \begin{aligned}
 \det(13K)
 &=343-14a^2-7b^2+2a^2b\\
 &=343-(14-2b)a^2-7b^2\\
 &<343-22\cdot25-7\cdot16=-319,
 \end{aligned}
\]

and

\[
 \boxed{\det K<-319/2197<0.}
\]

No Taylor approximation, floating eigensolver or uncertain decimal bound is needed. Thus the three-character moment test rejects this actual fibre while **all** single-mode tests accept it. This is a strict diagnostic hierarchy on one finite fibre; it says nothing about a uniform supply of such fibres in a hypothetical whole-cover family.

## 5. The actual current intersection is part of the interface

For the unmodified current class `1 mod11^12`, its intersection with `J=0 mod11^11` is empty. On that actual fibre the mean is

\[
 12/13+9/221-1=-8/221<0,
\]

so CP2 itself already rejects it. Replacing the current class by `11^11 mod11^12` gives a different family and restores a last-digit-1 child, but selected single modes passing in that modified example does not establish that *every* single mode passes. The 13-point construction above supplies that missing strict comparison directly and without silently changing an existing original label.

## 6. No fixed character count detects every conditional hole

Let `q>=7` be prime, put `H=2(q-1)-1`, and take `e=0,...,H` with

\[
 d_e=q3^e5^{H-e},\qquad
 a_e\equiv0\pmod{3^e5^{H-e}},\qquad
 a_e\equiv1+\lfloor e/2\rfloor\pmod q.
\]

These `2(q-1)` original moduli are distinct and odd. The private-witness
formula of section 2 applies with this `q,H` because `q` is coprime to15;
every label remains essential to the union. On the actual old fibre
`N=0 mod15^H`, all nonzero `q` residues occur exactly twice and zero never
occurs. Thus

\[
 g(z)=1-2\mathbf1_{\{0\}}(z),\quad
 \widehat g(0)=1-2/q,\quad
 \widehat g(k)=-2/q\quad(k\ne0).
\]

For **any** `s` distinct characters, their moment matrix is

\[
 K_s=I_s-\frac2q\mathbf1_s\mathbf1_s^*,
 \qquad
 \operatorname{spec}(K_s)=
 \{1\text{ with multiplicity }s-1,\ 1-2s/q\}.
\]

All tests supported on at most `s` characters therefore pass when
`2s<q`, although the fibre has an actual uncovered point. The first
detecting character count is `(q+1)/2`. For `q=7`, every three-character
matrix is positive definite and a four-character matrix has a negative
eigenvalue. Given any fixed character budget, a larger prime supplies
the same obstruction.

This is a limitation on conditional tests using that many characters,
not on unrestricted functions or on all possible old-fibre observations.
In particular, passing a three-character scan does not imply that the
remaining obstruction uses three distinct future primes: this example
has only one future prime. Full character information still detects
the hole. All these families already have the uncovered integer zero;
none is a counterexample to odd noncoverage.

## 7. A negative quadratic gives a same-source mass certificate

For the literal nonnegative integer multiplicity `N` of section 1, put
`U={N=0}`. Then `g=-1` on `U` and `g>=0` off `U`. For any test `h` and
any bound `0<B` with `|h|^2<=B` on the complete fibre,

\[
 \mathbb E[g|h|^2]\ge -B\Pr(U),\qquad
 \Pr(U)\ge \frac{[-\mathbb E(g|h|^2)]_+}{B}.       \tag{FP1}
\]

No covering assumption is used in FP1. In the20-label example,
`|h|^2<=9` by the triangle inequality, so its relative uncovered density
is greater than `7/117`; the exact density is `3/13`. The old fibre has
Haar mass `1/15^19`, which must be included in a full-period bound.

More generally let `eta` be any finite measure on genuine old survivors.
At each old state use any subset of disjoint depth-`t` prefixes `J`,
with the exact original pullbacks, a chosen `h_(x,J)` and a positive
bound `B_(x,J)`. Write `s_(x,J)` for the corresponding relative Haar
quadratic expectation. Integration gives

\[
 (\eta\times\mathrm{Haar}_{\rm remaining})(\mathrm{uncovered})
 \ge
 \int\sum_{J\ \mathrm{selected}}p^{-t}
       \frac{[-s_{x,J}]_+}{B_{x,J}}\,d\eta(x).      \tag{FP2}
\]

This law is the declared old-measure-times-Haar law; it is not an
unproved replacement for the later physical or killed chain. The same
original `eta` appears on both sides and no witness counts reweight it.
Positive right side gives a real uncovered CRT integer. Under whole
coverage, every local moment matrix, and every nonnegative weighted
integral of them against this same `eta`, is positive semidefinite.

FP2 does not prove the existence of a useful test on positive `eta`
mass for arbitrary original families. A completely covered conditional
fibre has nonnegative multiplicity surplus, and an exactly covered
fibre has zero surplus and zero moment matrices. The locally complete
constructions in340 therefore retain their stated obstruction to a
purely local universal argument.

## 8. Original maximal conductors give a joint necessary constraint

For a finite family with distinct original moduli `d_i>1`, this section
uses full-period Haar and
`H_cov=sum_i 1/d_i-1`, not339's effective9 source parameter `rho`.
Let `T` be a nonempty set of divisibility-maximal original moduli. For
every prime `p` and **positive** exponent `e`, assume

\[
 |\{d\in T:v_p(d)=e\}|\le p-1.                  \tag{FP3}
\]

Choose a primitive character of each conductor `d` as follows. At every
fixed `(p,e)` assign distinct nonzero leading units modulo `p` to the
moduli having that exponent. On unequal exponents a ratio automatically
retains the larger exponent; on equal positive exponents the distinct
units prevent cancellation. CRT therefore gives characters `chi_d`
with

\[
 \operatorname{cond}(\chi_d\overline{\chi_f})
   =\operatorname{lcm}(d,f)\quad(d\ne f).
\]

No original modulus is a multiple of this LCM: it would strictly
dominate a divisibility-maximal original modulus. Consequently the
off-diagonal Fourier coefficients between these characters vanish.
The coefficient between the constant character and `chi_d` has modulus
`1/d` by original-modulus uniqueness, exactly as in336. Under whole
coverage their moment matrix has block form

\[
 K=\begin{pmatrix}H_{\rm cov}&a^*\\
                  a&H_{\rm cov}I\end{pmatrix},
 \qquad |a_d|=1/d.
\]

Its positivity forces

\[
 \boxed{H_{\rm cov}\ge\left(\sum_{d\in T}d^{-2}\right)^{1/2}.} \tag{FP4}
\]

Indeed its extremal eigenvalues are `H_cov +/- ||a||_2`. For any two
distinct maximal odd moduli, FP3 holds because `p-1>=2`, giving
`H_cov^2>=d_1^-2+d_2^-2`. The single-label case is the existing336 bound.
The joint constraint is a short consequence of finite Fourier positivity;
it is not a claim of a new literature theorem or new Lean content.

There is no established unrestricted upper bound on `H_cov` contradicting
FP4. A family may have only one maximal modulus. Applying FP4 to residual
moduli requires checking their actual multiplicities afresh; original
uniqueness is not inherited by conditional pullback. Nor may `H_cov` be
identified with a distorted source surplus.

## 9. Exact verification and scope

The [standalone standard-library program](../../frontier/whole-cover/original_fourier_moments.py)
constructs the actual original labels, private integers and physical
CRT fibres. It verifies Fourier identities as integer polynomials modulo
the prime cyclotomic relation, not by floating-point eigenvalues. Its
default rank examples use `q=7,11,17`. Together with the20-label example
they give1,968 private-point membership checks and1,108 literal fibre
checks. It also verifies an explicit simultaneous maximal-conductor
choice for `(45,63,175)` in period1575. It writes no files and accepts
`--rank-primes` for other declared primes.

The trigonometric inequalities and arbitrary-prime rank formula above
are ordinary proofs. The program verifies their exact polynomial and
rational premises; it is not a Lean verification of those proofs.
Finite Gram positivity, Fourier orthogonality and the eigenvalues of a
rank-one update are standard. These original-label applications retain
their assumptions and give neither a new unrestricted family exclusion
nor a complete test at fixed rank. No Lean declaration, build or freeze
is claimed.
