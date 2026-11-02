---
slug: lester-haddadin-gripaios-2022-chiral-event-parity-minimality
bibkey: lesterhaddadingripaios2022parity
doi: 10.1142/S0217751X22500932
url: https://arxiv.org/abs/2008.05206v6
triage: theorem
motivation_gids:
  - D5/S3/Geometry/Lorentz/ChiralEventParityMinimality.result
---

# Three continuous invariant parity-odd variables are necessary for two interchangeable pairs

## Problem

C. G. Lester, W. Haddadin and B. Gripaios, *Lorentz and permutation invariants of particles III: constraining non-standard sources of parity violation*, Int. J. Mod. Phys. A 37(16) (2022) 2250093, arXiv:2008.05206v6, Introduction, `introduction.tex`, lines 103–104:

> No claim is made that either set $S$  or $\hat S$ is globally \textbf{minimal} for the class of events with which it is concerned.  That is to say:  it has not been proved that there does not exist some other set $S_?$ containing only one or two event variables but which retains all the  stated properties.
> Nonetheless, we \textit{conjecture} that there is indeed  no smaller set $S_?$ and that $S$ and $\hat S$ are therefore examples of \textbf{minimal} sets.

The quotation is from the downloaded v6 TeX member `introduction.tex` (md5 `2b21a1456fcb7bb5df295f300f8b61ae`). The definitions and source locators are collected in [the literature note](../Library/Geometry/lesterhaddadingripaios2022parity.md).

An event is an ordered quadruple $(p,q,a,b)$ of real four-vectors. Write $u\cdot v=u_0v_0-u_1v_1-u_2v_2-u_3v_3$ and $u^2=u\cdot u$. The forward cone consists of vectors with $u_0\ge0$ and $u_1^2+u_2^2+u_3^2\le u_0^2$, including zero. The two domains are:

- $\Omega_{(pq)(ab)X}$: all quadruples of forward-cone vectors (`allEvents`);
- $\Omega_{(pq)\to(ab)X}$: those quadruples additionally satisfying $p^2q^2<(p\cdot q)^2$ (`collisionEvents`).

The symmetry uses a common matrix $\Lambda$ satisfying $\Lambda^{\mathsf T}\eta\Lambda=\eta$, $\det\Lambda=1$ and $\Lambda_{00}>0$, where $\eta=\operatorname{diag}(1,-1,-1,-1)$, together with independent permutations of $(p,q)$ and $(a,b)$. Parity $\mathscr P$ fixes each energy and negates each spatial momentum. An event is chiral when no such symmetry carries it to its parity image. These match `prelims.tex`, lines 25–27, 190–193, 228–243, 265–268, 433–443 and 656–666; neither domain adds momentum conservation or fixed masses.

Issue [#25338](https://github.com/the-omega-institute/trureturing/issues/25338) fixes the assertion: for either domain and every pair $f_1,f_2:\mathrm{event}\to\mathbb R$ continuous on that domain, invariant under these symmetries there, and parity odd there, some chiral event in the domain satisfies $f_1=f_2=0$. This assertion is proved.

## Motivation

The source seeks finite sets of observables that detect every chiral event while respecting the Lorentz and permutation symmetries. Its sufficiency requirement is that at least one observable be nonzero at every chiral event (`goals.tex`, lines 11–12). Its three-variable sets $S$ and $\hat S$ supply candidate optimal sizes for the full and collision domains respectively. A universal common-zero obstruction for two observables rules out every smaller sufficient set, including nonlinear choices unrelated to the displayed variables.

## Gap

The bounded literature check recorded in #25338 reports:

- the conjecture remains in arXiv v6, which is also the source text checked here;
- INSPIRE record 1811414 listed six citing records, and the orchestrator downloaded and searched the TeX of arXiv:2111.00623, 2111.00616, 2205.09876 and 2512.23750 without finding a two-variable lower bound settling this conjecture;
- the orchestrator's repository and issue searches found no existing settlement.

`not-found-in-searched-scope`. The citation searches are reported evidence from the preregistration, not an exhaustive literature classification.

## Route

Let $S^2=\{v\in\mathbb R^3:\|v\|=1\}$. For $v=(s,t,d)$, `family` defines $e_v=(p,q,a_v,b_v)$ by

$p=(30,0,0,1),\qquad q=(20,0,0,-1),$

$a_v=(10+s,\sqrt{4+t},0,d),\qquad b_v=(10-s,0,\sqrt{4-t},-d).$

1. **A continuous chiral collision sphere.** For every $v\in S^2$, `family_mem_all` proves $e_v\in\mathrm{allEvents}$, `family_mem_collision` proves $e_v\in\mathrm{collisionEvents}$, and `family_chiral` proves that $e_v$ is chiral. `family_continuous` proves continuity of this family on $S^2$. All three pointwise assertions require the unit-sphere hypothesis; the family is defined on all of $\mathbb R^3$.
2. **The antipodal symmetry.** For every $v\in\mathbb R^3$, `family_neg` proves $e_{-v}=\operatorname{act}(R,\mathrm{id},(ab))(\mathscr P e_v)$, where `rotation` is $R(E,x,y,z)=(E,-y,-x,-z)$. `rotation_proper` proves that $R$ satisfies all three defining Lorentz-matrix conditions. For every event $x$, `parity_all_iff` and `parity_collision_iff` prove that parity preserves membership in the respective domains.
3. **Pullback of admissible variables.** For any event domain $\Omega$ containing `collisionEvents` and any pair $f_1,f_2$ each satisfying `admissible Ω`, `family_admissible_zero` proves that $F(v)=f_1(e_v)+i f_2(e_v)$ is continuous on $S^2$. Under the same domain-inclusion hypothesis, for every admissible real $f$ and every $v\in S^2$, `family_admissible_odd` proves $f(e_{-v})=-f(e_v)$ after inclusion into $\mathbb C$. Thus $F$ is odd on $S^2$.
4. **A common zero.** The private `planar_odd_map_zero`, Borsuk's Satz II (1933) for $n=2$ applied to odd maps (`Library/Topology/borsuk1933spheres.md`) and proved in the module from the covering-space lift of the circle, states that every $F:\mathbb R^3\to\mathbb C$ continuous on $S^2$ and satisfying $F(-v)=-F(v)$ for every $v\in S^2$ has a zero on $S^2$. Applying it to the pullback, then taking real and imaginary parts, gives both real zeros at the chiral event $e_v$. `result` assembles these facts for `allEvents` and `collisionEvents`, each of which contains `collisionEvents`.

## Falsifier

A common zero at an achiral event would not obstruct sufficiency. The witness here lies in the family whose chirality is proved for every unit-sphere parameter by `family_chiral`. The assertion also quantifies over every admissible pair, rather than only deletions from the source's chosen triple.

The formal notion of admissibility requires continuity, invariance and parity oddness only on the selected domain; the observables themselves are functions on the ambient event type. The matrix conditions, pair permutations, parity and strict collision inequality are those specified above. No assertion about discontinuous observables or a domain with additional mass or momentum constraints is included. The three-variable upper bound is not a declaration of this module.

## Evidence

The canonical source is `D5/S3/Geometry/Lorentz/ChiralEventParityMinimality.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Geometry/Lorentz/ChiralEventParityMinimality.lean.json`.

Declaration statements:

- `result`: `sha256:63df8887e38c9c69db9245420fa8ea2d0070fe0a5deba2e9abdf01a254fe4aaa`;
- `claim`: `sha256:1f8bafc17e84c44dfdcf82cead206181234e83d0502c61ced1be015f6a9a7d92`.

## Triage

Tier 1 conjecture of a 2020 arXiv paper published in 2022, preregistered in issue #25338 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for each of `allEvents` and `collisionEvents`, every pair of real-valued functions on the ambient event type that are continuous on that domain, invariant there under every allowed Lorentz matrix and both independent pair permutations, and parity odd there, has a common zero at some chiral event in that domain.

**Computed, not formalized:** None.

**Argued, not formalized**.

- *Decisive mechanism.* The continuous chiral sphere and its antipodal parity relation force every admissible pair to pull back to a continuous odd planar map, under exactly the hypotheses of the Route lemmas. The planar zero theorem forces an unwanted zero regardless of the formula used for either observable. This supplies a structural obstruction to compression into two real variables.
- *Extension.* For any event domain $\Omega$ containing `collisionEvents`, and any two ambient real functions satisfying `admissible Ω`, the same conclusion follows: `family_mem_collision` and `family_chiral` give membership and chirality at every unit-sphere parameter, the inclusion puts those events in $\Omega$, `family_admissible_zero` and `family_admissible_odd` give a continuous odd pullback, and `planar_odd_map_zero` gives a common zero. This generalization is a consequence of the Route, not the stated type of `result`.
- *Sharpness and the source's conjecture.* Taking $f_2=f_1$ rules out a sufficient singleton as well. Combining this lower bound with the source's sufficient three-element sets gives minimum cardinality exactly three on both domains. The upper bound is supplied by the source: `pqabAll-variables.tex`, lines 11–24, states sufficiency of $S$ for every nonzero real choice of its parameters $u_1,u_2$, and lines 234–269 give the corresponding collision-only hatted construction. Those constructions and their sufficiency are not formalized here.
- *Why continuity matters.* Given any finite sufficient family of invariant parity-odd real observables, choose the first nonzero value in a fixed order, or zero if none exists. Each zero test is invariant and unchanged by parity, so the selected index is invariant and the same at an event and its parity image; the selected value is consequently invariant, parity odd, and nonzero at every chiral event. On either domain of `result`, such a selector cannot also be continuous, since applying `result` to two copies of it would contradict sufficiency. This explains the source's selector construction in `main.tex`, lines 199–210, without claiming a formalization of it.
- *Range and neighbouring questions.* The theorem gives an existential blind spot for each pair, with no prescribed masses, energy scale, or quantitative lower bound on the size of the blind set. Restricting to a fixed-mass, equal-mass, massless or momentum-conserving subdomain can remove the displayed sphere; the minimum number on such a subdomain remains open here. The three-variable lower bound therefore does not contradict the source's restricted entirely massless example in `main.tex`, line 285.
- *Effect on dependent claims.* The lower bound supplies the missing minimality argument for $S$ and $\hat S$, conditional on their source-established upper bounds. For these two domains it also excludes the single continuous sufficient parity contemplated in `main.tex`, lines 173–193. The source's sufficiency and event-selection arguments receive no additional formal verification, and its separate $S_{19}$ and $S_{28}$ questions are not settled.

## ASSUMED-UNVERIFIED

The bounded literature check in #25338 does not establish exhaustive worldwide novelty or priority. Its INSPIRE citation listing, searches of the four citing papers, and repository searches were performed by the orchestrator and were not independently reproduced. The journal text was not read; retention of the conjecture in that text is unverified. The source's three-variable constructions and upper-bound proofs were read in arXiv v6 but were not reproduced or formalized.

The arguments and consequences in "Argued, not formalized" are not additional compiled declarations. Minimality on more restricted physical domains, the larger event classes, and empirical sensitivity or performance of any observable remain outside this settlement.
