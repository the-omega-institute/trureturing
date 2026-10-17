# Arithmetic holographic RT — continuation

Continuation of [ARITHMETIC_HOLOGRAPHIC_RT.md](ARITHMETIC_HOLOGRAPHIC_RT.md), retaining its notation for finite LOSR state conversion.

## 52. Exact Bell-source conversion error for maximally correlated qubit targets

### 52.1 Theorem (exact trace-norm optimum)

Let |Φ⁺⟩=(|00⟩+|11⟩)/√2 and Φ=|Φ⁺⟩⟨Φ⁺|, and let

τ=ρ(p,d)=p|00⟩⟨00|+(1−p)|11⟩⟨11|+d|00⟩⟨11|+conj(d)|11⟩⟨00|,

where 0≤p≤1 and |d|²≤p(1−p). Then

min_{Λ∈LOSR} ‖Λ(Φ)−τ‖₁ = √2 max{0, |d|−min(p,1−p)}.

The norm is unhalved. At most three product-CPTP branches attain the minimum. In the positive-error regime two suffice. The optimization includes outputs outside the maximally correlated subspace. Thus Bell-to-τ exact LOSR conversion holds if and only if |d|≤min(p,1−p).


LOSR means finite convex mixtures of product CPTP maps from two qubits to two qubits, with arbitrary local product ancillas, no additional shared entanglement, no communication, and no postselection.

**Fidelity support calculation within the proof.**

For u∈[1/2,1], write |ψ_u⟩=√u|00⟩+√(1−u)|11⟩. The squared pure-target fidelity has the exact support value

sup_{Λ∈LOSR} ⟨ψ_u|Λ(Φ)|ψ_u⟩ = max{u, 1/2+√(u(1−u))}.

Here squared fidelity means precisely the displayed expectation, avoiding the alternate square-root convention. The calculation is a specialization of the standard purification/Schmidt-coefficient method for pure-state conversion; it is included as an intermediate step, not claimed as a new standalone result.

It suffices to bound a product channel A⊗B, since the expectation is affine. Every qubit CPTP channel admits a finite Stinespring environment of dimension at most four (its Choi rank is at most four), so this representation also covers implementations originally using arbitrarily large or mixed local product ancillas. Stinespring isometries V_A:C²→C²⊗E_A and V_B:C²→C²⊗E_B purify its output as Ω=(V_A⊗V_B)|Φ⁺⟩. Across (A E_A):(B E_B), Ω still has exactly two Schmidt coefficients 1/√2,1/√2. Put v=(⟨ψ_u|⊗I_E)Ω. The target expectation is ‖v‖²=max_{‖e‖=1}|⟨ψ_u⊗e|Ω⟩|² (if v=0 this identity is immediate; otherwise take e=v/‖v‖). Thus no enlargement of the environment or attainment assumption is needed.

For an arbitrary normalized environment vector e with Schmidt probabilities r₁≥r₂≥⋯≥0, the Schmidt probabilities of ψ_u⊗e are {u r_i,(1−u)r_i}. Pad with zero probabilities if necessary. The largest two are u r₁ and max{(1−u)r₁,u r₂}. The singular-value trace inequality applied to the coefficient matrices of these two bipartite vectors gives

|⟨ψ_u⊗e|Ω⟩| ≤ [√(u r₁)+√(max{(1−u)r₁,u r₂})]/√2.

Indeed the coefficient matrix of Ω has singular values 1/√2,1/√2,0,…, while the singular values of the other coefficient matrix are its Schmidt coefficients, so |Tr(M†N)|≤Σ_i s_i(M)s_i(N) yields exactly this bound. All spaces may be padded to common rectangular dimensions.

If the second-largest product is (1−u)r₁, the square of the bound is r₁[1/2+√(u(1−u))]≤1/2+√(u(1−u)). If it is u r₂, the square is u(√r₁+√r₂)²/2≤u(r₁+r₂)≤u. These two cases exhaust ties as well. The bound holds for every e and hence every product channel and every finite LOSR mixture. Identity attains 1/2+√(u(1−u)); the product reset attains u. This proves the support calculation, including u=1/2 and u=1.

**Trace-norm proof and attainment.**

Proof. A local diagonal output unitary removes the phase of d, and simultaneous output bit flips exchange p and 1−p. These are invertible local operations; they preserve the LOSR output set from Φ and preserve trace norm, so assume p≥1/2 and d=w≥0. Put q=1−p.

If w≤q, all coefficients in

τ=2wΦ+(p−w)|00⟩⟨00|+(q−w)|11⟩⟨11|

are nonnegative and sum to one. Identity on both sides and simultaneous local resets to 0 or 1 realize this mixture, giving zero error.

If w>q, put t=w+q. Since positivity gives w≤√(pq)≤p, one has 0≤t≤1. The two-branch output σ_t=tΦ+(1−t)|00⟩⟨00| obeys

τ−σ_t=(w−q)/2·[[1,1],[1,−1]]

on span{|00⟩,|11⟩} and vanishes on its orthogonal complement. The eigenvalues are ±(w−q)/√2, so the trace norm is √2(w−q).

For the matching all-output lower bound use the witness H=2τ_s−I₄, where τ_s:=|ψ_s⟩⟨ψ_s| and s=(1+1/√2)/2. Its eigenvalues are 1,−1,−1,−1, so ‖H‖∞=1. Its matrix on span{|00⟩,|11⟩} is (1/√2)[[1,1],[1,−1]], and on the orthogonal complement it is −I₂. The support calculation gives Tr Hσ≤1/√2 for every LOSR output σ from Φ. On the target Tr Hτ=(2p−1+2w)/√2. Thus norm duality gives ‖τ−σ‖₁≥√2(w+p−1)=√2(w−q); combining with nonnegativity covers both regimes. Phase restoration and swaps finish the proof.


### 52.2 Theorem (nonflat pure-target specialization)

For d=√(p(1−p)) and p∈[1/2,1], the theorem gives δ=√2(√(p(1−p))+p−1). It is strictly positive for 1/2<p<1: the squared difference p(1−p)−(1−p)²=(1−p)(2p−1)>0 implies √(p(1−p))>1−p. It vanishes at both endpoints, attained by identity at p=1/2 and reset at p=1. For arbitrary p use max(p,1−p).

For the Bell source, the population interval in RT §51 is the singleton p=1/2. Its negativity-deficit bound vanishes for every physical target here, so it cannot certify the positive error in this corollary. The present witness gives the exact value, rather than only a compactness obstruction.

**Scope of Theorems 52.1–52.2.**

This exact trace-distance formula concerns the full physical two-qubit maximally correlated target family. After phase alignment, its zero-error diamond geometry is a slice of prior PIO reachability, after the known maximally correlated lift. See Shi et al., Scientific Reports 7,14806 (2017), Eqs.(31)–(32) and Fig.3, https://www.nature.com/articles/s41598-017-13687-4 , and Chitambar–Gour, Phys. Rev. A 94,052336 (2016), discussion after Proposition3, https://link.aps.org/accepted/10.1103/PhysRevA.94.052336 . The additional proof here is the unrestricted-output trace-norm optimality via a supporting pure-target fidelity witness. No priority claim is made for that geometry or construction. The state source is exactly one Bell pair; arbitrary mixed source states, catalysts, communication, and coherent multisector channels remain outside scope.

**Mathematical sources.**

The purification/Schmidt comparison follows the standard local-isometry representation of pure-state conversion, as used by George–Chitambar, Phys. Rev. A 109,062418 (2024), Theorem4 and the general dilution optimization in Proposition11: https://link.aps.org/accepted/10.1103/PhysRevA.109.062418 . The present proof establishes the needed two-Schmidt-value support bound explicitly. No literature priority is claimed for the support calculation, purification argument, trace-norm duality, or the identity/reset construction. The conclusion is the exact trace-norm optimum with a matching all-output witness and an explicit attainer.

## 53. Pure two-qubit source to arbitrary maximally correlated target

### 53.1 Theorem (complete pure-source trace-norm optimum)

Let R∈[1/2,1], Q=1−R, C=√(RQ), and let the source be σ_R=|ψ_R⟩⟨ψ_R| with |ψ_R⟩=√R|00⟩+√Q|11⟩. For the physical target τ=ρ(p,d) from §51, set P=max(p,1−p), q=1−P, and w=|d|. Let LOSR denote finite convex mixtures of product qubit CPTP maps, with local product ancillas, no additional shared entanglement, no communication, and no postselection. Then the exact unhalved Schatten trace-norm error is

δ = 2 max(0,w−C), if P≤R;

δ = 2 max(0,√Q w−√R q), if P≥R.

At P=R the two expressions agree: physical w≤C makes both zero. At R=1 the first branch covers every target and gives δ=2w; at R=1/2 the second gives the Bell theorem. Target phases and interchange of p,1−p can be absorbed into local output unitaries. No source modification is needed for these output-set symmetries.

Every pure two-qubit source has this Schmidt form after local input unitaries; those can be absorbed into the allowed local channels without changing the optimum. The target is required to have the stated maximally correlated form in a chosen local output basis.

The first regime is exactly the already proved mixed-source interval theorem §51 specialized to the pure source, including arbitrary target phase. Its proof is not duplicated. It remains to prove the second regime for R<1.

**Fidelity support calculation within the proof.**

For u∈[1/2,1], every product-CPTP output ξ from σ_R obeys

⟨ψ_u|ξ|ψ_u⟩ ≤ max{u,(√(Ru)+√(Q(1−u)))²}.

Both bounds are attainable by reset and identity respectively, so the right side is also the exact LOSR support. Proof: finite local Stinespring isometries preserve source Schmidt coefficients √R,√Q. For an environment vector with decreasing Schmidt probabilities e₁,e₂,…, the largest two probabilities of ψ_u⊗e are u e₁ and max{(1−u)e₁,u e₂}. The same coefficient-matrix trace inequality as §52 bounds overlap by

√(R u e₁)+√(Q max{(1−u)e₁,u e₂}).

If the second product is (1−u)e₁, the squared expression is e₁(√(Ru)+√(Q(1−u)))². Otherwise it is u(√(R e₁)+√(Q e₂))²≤u(R+Q)(e₁+e₂)≤u. Maximizing over environment vectors gives the stated fidelity bound for every product channel; affinity gives all finite LOSR mixtures. Finite environments of dimension≤4 on each side cover every qubit CPTP channel.

**Lower bound for P≥R.**

Put u=(1+√R)/2, so 2u−1=√R and 2√(u(1−u))=√Q. The two fidelity bounds coincide: direct expansion of the local-unitary fidelity gives

(√(Ru)+√(Q(1−u)))² = Ru+Q(1−u)+2√(RQ)√(u(1−u)) = u.

Therefore H=2|ψ_u⟩⟨ψ_u|−I₄ has operator norm1 and Tr(Hξ)≤√R for every LOSR output ξ. Its MC block is [[√R,√Q],[√Q,−√R]], and its other block is−I₂. For target population P and real coherencew,

Tr(Hτ)=√R(2P−1)+2√Q w.

Trace-norm duality gives δ≥2(√Q w−√R q), and nonnegativity completes the asserted lower bound without restricting outputs.

**Attainment for P≥R.**

If w≤Cq/Q, let t=w/C. For R<1, C>0. The exact decomposition

τ=tσ_R+(P−tR)|00⟩⟨00|+(q−tQ)|11⟩⟨11|

has nonnegative weights. Indeed t≤q/Q≤1, q−tQ≥0, and P−tR≥P−Rq/Q=(P−R)/Q≥0. Their sum is1. Three shared product-CPTP branches, identity and the two local resets, attain zero. The condition is equivalent to √Q w≤√R q.

If w>Cq/Q, set t=q+w√(R/Q). One has t≥0. Physicality w²≤Pq and P≥R imply w≤P√(Q/R), since Rq≤PQ is equivalent to R≤P. Therefore t≤q+P=1. Use ξ_t=tσ_R+(1−t)|00⟩⟨00|. Put b=√Q w−√R q>0. Its target difference in the MC basis is

τ−ξ_t=b[[√R,√Q],[√Q,−√R]].

To check: the diagonal entry is−q+tQ=−Rq+w√(RQ)=√R b, and the off-diagonal entry is w−tC=Qw−q√(RQ)=√Q b. The displayed matrix has eigenvalues±b because R+Q=1; its trace norm is2b. This attains the lower bound with two product-CPTP branches. The product-source endpoint R=1 was already handled by the first regime. Thus all parameters and endpoints are covered.

**Scope.**

This is a full pure-two-qubit-source/maximally-correlated-target trace-norm conversion formula under finite LOSR, with no constraint on output support in the optimization. General mixed sources outside the §51 population interval remain open. The fidelity/Schmidt calculation is a direct specialization of the standard pure-state conversion framework, and the source/reset reachability geometry has PIO predecessors; no novelty is claimed for those ingredients.

**Mathematical sources.**

The purification and Schmidt-coefficient method follows George–Chitambar, Phys. Rev. A 109,062418 (2024), Theorem4, https://link.aps.org/accepted/10.1103/PhysRevA.109.062418 . Its use here is proved directly with the two largest Schmidt products; fidelity is the squared convention ⟨ψ_u|ξ|ψ_u⟩. Source/reset reachability is related to the qubit PIO region of Shi et al., Scientific Reports 7,14806 (2017), Eqs.(31)–(32), Fig.3, https://www.nature.com/articles/s41598-017-13687-4 , and its zero-communication maximally correlated lift described by Chitambar–Gour, Phys. Rev. A 94,052336 (2016), after Proposition3, https://link.aps.org/accepted/10.1103/PhysRevA.94.052336 . No priority claim is made for these ingredients or the reachability construction. The conclusion here is the exact trace-norm value with an unrestricted-output lower bound and attainment on the stated source/target family.
