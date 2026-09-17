[Index](../../../../Problems/erdos-7-odd-covering-systems.md) · [Previous](08-arbitrary-head-transfer-by-the-joint-load-invariant.md) · [Next](10-a-four-prime-head-and-a-restricted-noncoverage-theorem.md)

<a id="quantitative-extension-of-the-old-prime-powers"></a>
### Quantitative extension of the old prime powers

Let `P` be a finite prime set and
`Q₀=∏_{p∈P}p^{H_p}`, `Q=∏_{p∈P}p^{K_p}`, where `K_p≥H_p≥1`.
Take any distinct-modulus family of nonunit divisors of `Q`. Suppose `μ`
is a probability avoiding every actual class whose modulus divides `Q₀`,
and `Γ_{Q₀}(μ)≤C`. Write

\[
 n_p=K_p-H_p,\quad k_p=H_p+1,\quad
 u_p=\sum_{t=1}^{n_p}p^{-t},\quad
 v_p=\sum_{t=1}^{n_p}(2t-1)p^{-t},\quad
 D_S=\prod_{p\in S}k_p,
\]
\[
 B=\prod_{p\in P}\left(1+\frac{2u_p}{k_p}+\frac{v_p}{k_p^2}\right),
\qquad
 \lambda=\sum_{\varnothing\ne S\subseteq P}\left(\prod_{p\in S}u_p\right)
 \min\left\{\frac{\sqrt C}{D_S},\frac{C}{D_S^2},
                    \frac{C-1}{D_S^2-1}\right\}.
\]

**Height-lifting theorem.** If `λ<1`, the complete family has a survivor,
and a probability `μ'` on its complete survivors satisfies

\[
 \boxed{\Gamma_Q(\mu')\le\frac{CB-\lambda}{1-\lambda}.}
 \tag{H1}
\]

**Proof.** Fix nonempty `S⊆P`. Let `F_S` be a partial core layout whose
moduli have exponent `H_p` at each `p∈S`. Project each selected class to all
`D_S` divisors obtained by independently lowering these exponents. All projected
moduli are distinct: the outside exponents identify the original modulus and
the inside exponents identify the projection. Complete the resulting selection
to a full core layout. Its load `L` satisfies `L≥D_S F_S` and `L≥1`. Thus

\[
 \mathbb E_\mu F_S^2\le C/D_S^2,\qquad
 \mathbb E_\mu F_S\le
 \min\{\sqrt C/D_S,\ C/D_S^2,\ (C-1)/(D_S^2-1)\}.
 \tag{H2}
\]

The first first-moment bound is Cauchy–Schwarz. The second uses the integral
inequality `F_S≤F_S²`. For the third, if `F_S=0` then `L²−1≥0`, and otherwise
`L²−1≥D_S²F_S²−1≥(D_S²−1)F_S`. For `S=∅` only the second-moment bound is
needed, with `D_∅=1`.

Extend `μ` uniformly over fibres of the reduction `Q→Q₀`, giving `ν`.
Group the actual future moduli by their excess vector
`t_p=max(v_p(d)−H_p,0)`. For fixed `t`, the reduced modulus `gcd(d,Q₀)`
determines `d` uniquely, so the reduced classes form a partial layout of the
kind in (H2), with `S=supp(t)`. Its conditional fibre mass is at most
`(∏p^{−t_p})F_t(x)`. Summing (H2) over nonzero excess vectors bounds the
union of all future excluded classes by a mass `b≤λ`.

For an arbitrary full test layout on `Q`, group its classes by the same
excess vectors, including `t=0`. For two fine moduli `d,e`, a compatible
intersection has modulus `lcm(d,e)` and occupies a fraction

\[
 \frac{\gcd(\operatorname{lcm}(d,e),Q_0)}{\operatorname{lcm}(d,e)}
 =\prod_p p^{-\max(t_p,s_p)}
\]

of a compatible coarse fibre; an incompatible intersection has mass zero.
Consequently (H2) and Cauchy–Schwarz bound the contribution of two groups by

\[
 C\frac{\prod_p p^{-\max(t_p,s_p)}}{D_{\operatorname{supp}(t)}
                                               D_{\operatorname{supp}(s)}}.
\]

Summing factorizes over primes. The pair `(0,0)` contributes one, the two
zero/nonzero cases give `2u_p/k_p`, and the positive/positive cases give
`v_p/k_p²`, because there are `2h−1` positive exponent pairs with maximum `h`.
Hence `Γ_Q(ν)≤CB`. This fibre count does not assume independent old coordinates
or an integer lift independent of the coarse residue.

Finally condition `ν` on avoiding every future forbidden class. The old
forbidden classes already have zero mass. Every full test load is at least
one, so

\[
 \mathbb E_{\mu'}L^2
 \le\frac{CB-b}{1-b}
 \le\frac{CB-\lambda}{1-\lambda}.
\]

The last inequality uses `CB≥1`. The new coarse marginal is proportional to
`μ(x) Pr(future survival | x)`. A completely killed fibre receives mass zero;
no preservation of all coarse fibres is assumed. This proves (H1).

**Finite sufficient targets.** Uniformly over all future heights,
`u_p≤1/(p−1)` and `v_p≤(p+1)/(p−1)²`. Take the twenty odd primes through 73
and common initial height `H`. If `e_j` is the elementary symmetric polynomial
in the twenty numbers `1/(p−1)`, valid majorants are

\[
 B_H=\prod_{p\in P}\left(1+\frac{2}{(H+1)(p-1)}+
                         \frac{p+1}{(H+1)^2(p-1)^2}\right),\qquad
 \lambda_H(C)=(C-1)\sum_{j=1}^{20}\frac{e_j}{(H+1)^{2j}-1}.
\]

The integer-valued estimate in (H2) suffices for this `λ_H`; no claim that it
is always the smallest of the three bounds is needed. Exact rational arithmetic
gives the following sufficient parameters. Display intervals have width
`10^−12` and contain the exact value `(CB_H−λ_H(C))/(1−λ_H(C))`.

| Hypothetical uniform base bound `C` | Exponent cap `H` | Upper display endpoint |
|---:|---:|---:|
| 128 | 71 | 138.742060391592 |
| 130 | 82 | 138.846691940509 |
| 138 | 543 | 138.875287923953 |
| 138.874 | 141476 | 138.876999989088 |

[The calibration verifier](../elementary-checks/verify_height_lifting_bounds.py)
checks `λ_H<1`, the strict bound below `138877/1000`, and the display intervals
using rational arithmetic. Run it from the repository root:

```sh
python3 docs/reports/erdos7-odd-covering/elementary-checks/verify_height_lifting_bounds.py
```

For example, a theorem that **every** distinct-modulus family with moduli
dividing `∏_{3≤p≤73}p^{71}` admits a survivor probability of `Γ≤128` would,
by (H1) and the preceding transfer, prove the negative answer to unrestricted
Erdős #7. Lower heights in an arbitrary target family can be padded to 71
without adding forbidden classes. The same applies to each other row.
**Every universal finite-base bound in this table is false.** Its cap is at
least 31, so the star construction directly applies and forces `Γ>139.59`,
strictly above each proposed `C`. The calibration remains a correct sufficient
implication; it is not a verification of all residue assignments. The height-lifting argument is not formalized in Lean.

<a id="one-stage-smoothing-of-the-height-lift"></a>
### One-stage smoothing of the height lift

Averaging the highest old digits before the final conditioning improves the
height error to `O(H⁻²)`. Fix a finite prime set `P` and
`1≤h_p≤H_p≤K_p`. Put

\[
 Q_h=\prod_p p^{h_p},\quad Q_H=\prod_p p^{H_p},\quad
 Q_K=\prod_p p^{K_p},\qquad r_p=H_p-h_p,\quad k_p=h_p+1,
 \quad D_S=\prod_{p\in S}k_p.
\]

Take a family of distinct nonunit moduli dividing `Q_K`. Suppose a probability
`μ` on `Z/Q_H Z` avoids every actual class whose modulus divides `Q_H`, and
`Γ_{Q_H}(μ)≤C`. For a vector `n` of nonnegative integers define

\[
 u_p(n_p)=\sum_{t=1}^{n_p}p^{-t},\qquad
 v_p(n_p)=\sum_{t=1}^{n_p}(2t-1)p^{-t},\qquad
 B_h(n)=\prod_p\left(1+\frac{2u_p(n_p)}{k_p}
                            +\frac{v_p(n_p)}{k_p^2}\right).
\]

Use `u_p(∞)=1/(p−1)` and `v_p(∞)=(p+1)/(p−1)²` in the infinite-height
expressions, and set

\[
 E_h(r)=B_h(\infty)-B_h(r),\qquad
 \lambda_h(C)=\sum_{\varnothing\ne S\subseteq P}
 \left(\prod_{p\in S}\frac1{p-1}\right)
 \min\left\{\frac{\sqrt C}{D_S},\frac C{D_S^2},
                         \frac{C-1}{D_S^2-1}\right\}.
\]

**Smoothed height-lifting theorem.** If `λ_h(C)<1`, there is a probability
`μ'` on complete survivors of the whole family such that

\[
 \boxed{\Gamma_{Q_K}(\mu')\le
       \frac{C[1+E_h(r)]-\lambda_h(C)}{1-\lambda_h(C)}.}
 \tag{S1}
\]

For finite `K`, replacing every `∞` by `K_p−h_p` in the corresponding local
sums gives the same assertion with smaller bounds. With `r=0`, (S1) is (H1).
No Γ-minimizing property of the initial law is assumed.

**Proof.** Let `η` be the projection of `μ` to `Q_h`; completing a coarse
layout to an old layout gives `Γ_{Q_h}(η)≤C`. Average `μ` over the additive
group `ker(Z/Q_H Z→Z/Q_h Z)`. Its average `ρ` is the uniform extension of `η`
to `Q_H`. Each translation takes a residue class to another class of the
same modulus, so Γ is translation invariant. It is also convex in the law,
being a maximum of linear expectations. Consequently `Γ_{Q_H}(ρ)≤C`.
The average can reintroduce old forbidden classes above the coarse cap;
these are included in the final conditioning. Classes with moduli dividing
`Q_h` remain avoided because the translations fix the coarse residue.

Extend `ρ` uniformly to `Q_K`, giving `ν`, equivalently the uniform extension
of `η` from `Q_h`. In a full test layout, the squared load from moduli dividing
`Q_H` has expectation at most `C`. Group all moduli by their excess vectors
`t_p=max(v_p(d)−h_p,0)`. The coarse modulus and `t` determine `d`, so each
coarse group is a partial layout to which (H2) applies at cap `h`. The same
CRT intersection count and Cauchy–Schwarz bound each ordered pair of groups by

\[
 C\frac{\prod_p p^{-\max(t_p,s_p)}}
        {D_{\operatorname{supp}(t)}D_{\operatorname{supp}(s)}}.
\]

Two groups are both old exactly when `t_p,s_p≤r_p` for every `p`.
The sum of coefficients over all other ordered pairs is
`B_h(K−h)−B_h(r)≤E_h(r)`. Adding the separately bounded old-old expectation
therefore gives `Γ_{Q_K}(ν)≤C[1+E_h(r)]`. This subtracts only explicit
coefficient sums, not an unknown old expectation.

Now group **all** actual excluded classes above `h`, including the old ones
that averaging reintroduced. Uniform fibre counting and the first-moment
part of (H2) give their total union mass `b≤λ_h(C)`. All remaining actual
classes already have zero mass. Condition once outside this union. Every
test squared load is at least one, so the resulting complete survivor law obeys

\[
 \Gamma_{Q_K}(\mu')\le
 \frac{C[1+E_h(r)]-b}{1-b}
 \le\frac{C[1+E_h(r)]-\lambda_h(C)}{1-\lambda_h(C)}.
\]

The last function is increasing in `b` because `C[1+E_h(r)]≥1`.
This proves (S1), without independent old coordinates or positive survival
in every old fibre.

**Two constants.** If the same initial law has the separately available bounds
`Γ_{Q_H}(μ)≤C_H` and `Γ_{Q_h}(η)≤C_h`, with `1≤C_h≤C_H`, only the old-old
term uses `C_H`. Thus, when `λ_h(C_h)<1`, the proof gives

\[
 \boxed{\Gamma_{Q_K}(\mu')\le
 \frac{C_H+C_hE_h(r)-\lambda_h(C_h)}{1-\lambda_h(C_h)}.}
 \tag{S2}
\]

**Rate.** For fixed `P,C`, choose common `H_p=H`,
`r_p=⌈log_p H⌉` and `h_p=H−r_p` for sufficiently large `H`. The exact tails

\[
 u_p(\infty)-u_p(r)=\frac{p^{-r}}{p-1},\qquad
 v_p(\infty)-v_p(r)=p^{-r}
       \left(\frac{2r}{p-1}+\frac{p+1}{(p-1)^2}\right)
\]

give `E_h(r)=O(H⁻²)` and `λ_h(C)=O(H⁻²)`. Hence (S1) is
`Γ_{Q_K}(μ')≤C+O_{P,C}(H⁻²)`, uniformly over all finite future heights.

**Fixed rational parameters.** Put `k_min=min_p k_p` and
`R=k_min²/(k_min²−1)`. Since `1/(D_S²−1)≤R/D_S²` for nonempty `S`, the
following rational product is a valid replacement for `λ_h(C)`:

\[
 \overline\lambda_h(C)=(C-1)R
       \left[\prod_p\left(1+\frac1{(p-1)k_p^2}\right)-1\right].
\]

For the twenty odd primes through 73, use prime order
`(3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73)`.
The following fixed widths give sufficient parameters for (S1). Each upper
display endpoint lies less than `10⁻¹²` above the exact rational bound and
is strictly below `138877/1000`.

| Hypothetical uniform base `C` | Common cap `H` | Width vector `r` in prime order | Upper display endpoint |
|---:|---:|---|---:|
| 128 | 52 | `(3,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1)` | 138.556342372564 |
| 130 | 58 | `(3,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1)` | 138.599521198059 |
| 138 | 185 | `(5,4,3,3,3,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2)` | 138.872506575675 |
| 138.874 | 3118 | `(10,7,6,5,5,4,4,4,4,4,4,4,3,3,3,3,3,3,3,3)` | 138.876998901712 |

[The smoothed calibration verifier](../elementary-checks/verify_smoothed_height_lifting.py)
uses exact `Fraction` arithmetic to check the geometric tails, the old-old
coefficient boxes, `0≤λ̄_h<1`, the strict target comparisons and these display
intervals. It uses Python 3.9+ standard library only, with explicit failures
that remain active under `-O`:

```sh
python3 docs/reports/erdos7-odd-covering/elementary-checks/verify_smoothed_height_lifting.py
python3 -O docs/reports/erdos7-odd-covering/elementary-checks/verify_smoothed_height_lifting.py
```

For example, a universal survivor bound `Γ≤128` at common cap 52 would now
suffice for unrestricted #7 through (S1) and the preceding prime-tail transfer.
**Every universal finite-base bound in this table is false.** All caps are
at least 31, so the star construction forces `Γ>139.59` at each of them.
The squarefree `Γ<138.874` result does not supply the cap-3118 hypothesis.
The verifier checks the numerical implications, not all residue assignments;
the smoothing theorem and its two-constant version have not been formalized
in Lean.
