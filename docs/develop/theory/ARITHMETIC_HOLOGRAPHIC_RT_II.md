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
