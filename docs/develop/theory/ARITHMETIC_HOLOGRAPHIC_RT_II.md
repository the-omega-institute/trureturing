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

## 54. Full-support maximally correlated sources: exact LOSR output normal form

Let M_n = span{|ii>: 1 <= i <= n}, with projector P_n. Let rho be a density operator strictly positive on M_n and zero on its orthogonal complement. Equivalently rho >= lambda P_n for some lambda > 0. Input and output local dimensions are n and m. Finite LOSR means a convex combination of product CPTP maps from n to m, with arbitrary finite local environments and no communication.

### 54.1 Theorem: a single full-support source certifies the whole correlated input algebra

If a finite LOSR map Lambda sends rho to an operator supported in M_m, then every positive-weight product branch sends every operator supported in M_n to an operator supported in M_m. For each branch there are a function f:{1,...,n}->{1,...,m} and two positive semidefinite matrices G_A,G_B with diagonal entries 1, and with (G_A)_{ij}=(G_B)_{ij}=0 whenever i != j and f(i)=f(j), such that its restriction is

    |ii><jj| -> (G_A)_{ij}(G_B)_{ij} |f(i)f(i)><f(j)f(j)|.

Conversely, every such triple (f,G_A,G_B) is the restriction of a product CPTP map. Consequently the complete set of exactly reachable MC targets is the convex hull of these explicitly parameterized images of rho. The statement includes arbitrary reference systems: the restrictions are equal as linear maps, so their tensor products with an identity map are equal.

Proof. Put Q_m=I-P_m. Each branch output is positive, and the sum has zero Q_m trace, so each positive-weight branch has zero Q_m trace. Since rho >= lambda P_n and positive maps preserve order, the same holds for its image of P_n, hence for each |ii><ii| separately. Its image is the product state alpha_i tensor beta_i. A product state supported in M_m must equal |kk><kk| for one k: its support is supp(alpha_i) tensor supp(beta_i), and the only nonzero product vectors in M_m are multiples of |kk>. Thus alpha_i=beta_i=|f(i)><f(i)| for a common f.

Take local Stinespring isometries. Purity of each system marginal forces V_A|i>=|f(i)> tensor |a_i>, and V_B|i>=|f(i)> tensor |b_i>, with unit environment vectors. Isometry gives <a_j|a_i>=<b_j|b_i>=0 for distinct i,j in the same fiber of f. Define (G_A)_{ij}=<a_j|a_i> and similarly G_B. These matrices are PSD (the transpose/conjugate of the usual Gram convention is also PSD). Partial tracing gives the formula on every matrix unit. Conversely realize any such matrices by unit vectors with these overlaps. The fiber-zero conditions make both V maps isometries, so tracing their environments gives the required local CPTP maps. Environments of dimension at most n suffice. This proves both directions.

The hypothesis is positivity on M_n, not full rank on the whole n^2-dimensional bipartite space. It is essential to the single-state-to-channel inference. For example, with H the qubit Hadamard unitary, H tensor H maps the Bell vector to itself but maps |00> outside M_2; a pure Bell input therefore cannot certify preservation of all M_2.

### 54.2 Complete qubit exact-reachability corollary

Write rho(r,c)=r|00><00|+(1-r)|11><11|+c|00><11|+conj(c)|11><00|, with 0<r<1 and |c|^2<r(1-r). Set R=max(r,1-r), Q=1-R>0 and C=|c|. A physical target rho(p,d) is exactly reachable by finite LOSR if and only if

    |d| <= C min{1, p/Q, (1-p)/Q}.

This includes populations outside [Q,R]. If C=0, the condition is simply d=0, and every such target is obtainable by shared random product resets. If C>0, set z=|d|/C. Equivalent conditions are 0<=z<=1 and zQ<=p<=1-zQ.

Proof. Sort and phase-align the source by local input unitaries. In the normal form n=m=2, f is either a permutation or constant. A permutation branch has populations (R,Q) or (Q,R), and coherence magnitude at most C. A constant branch is a reset to |00> or |11>, with zero coherence. If total permutation weight is a, then |d|<=aC and both target populations are at least aQ. Thus |d|/C <= min(1,p/Q,(1-p)/Q).

Conversely choose permutation weight z. Mixtures of the two aligned permutation branches contribute population in [zQ,zR] and coherence exactly zC, after phase alignment. The remaining weight 1-z can be split between the two resets, expanding the achievable population interval to [zQ,zR+1-z]=[zQ,1-zQ]. Restore the desired coherence phase by a local diagonal unitary. At most four product CPTP branches suffice. This proves necessity over unrestricted product CPTP maps, rather than only over maps assumed to preserve M_2.

For a target outside this region, the minimum unhalved trace distance over finite LOSR is strictly positive: the compact set of product qubit channels has compact convex hull in a finite-dimensional vector space, so its image on rho is compact. This is a qualitative obstruction, not an explicit error formula or a claim that the closest output stays in M_2.

### 54.3 Attribution and scope

The qubit region has the familiar PIO reachable-hexagon geometry after phase alignment, as in Shi et al., Scientific Reports 7,14806 (2017), Eqs.31-32 and Fig.3: https://www.nature.com/articles/s41598-017-13687-4 . The connection from PIO to zero-communication MC transformations is discussed after Proposition 3 of Chitambar and Gour, Physical Review A 94,052336 (2016): https://link.aps.org/accepted/10.1103/PhysRevA.94.052336 . Neither the hexagon shape nor its constructive sufficiency is claimed as new. The argument above supplies a direct full-support, all-product-CPTP necessity and a dimension-independent channel restriction normal form. Literature priority for that normal form is not asserted.

The linear-map conclusion is a concrete coherent-input interface: once one full-support MC test state has exactly zero leakage, all coherent matrix units and arbitrary references obey the same normal form. It does not imply that independently chosen optimizers for separate RT sectors can be combined into one local physical channel. It does not prove the general mixed-source positive-error optimum, approximate support rigidity, or full RT recovery.

The original volume's §38.2 already gives a coherent-channel interface. The present result supplies a different sufficient certificate, namely strict positivity on the MC support together with exact zero output leakage; it is not claimed as the first coherent-input interface.

## 55. Sharp mixed-source positive-error family

### 55.1 Theorem (exact error on a mixed-source edge family)

Use unhalved trace norm and finite LOSR. Sort and phase-align a mixed MC qubit source rho(r,c), r>=1/2, q=1-r, q<=c<=sqrt(rq), q>0. Define D=sqrt(c^2+q^2), R*=c^2/D^2, Q*=q^2/D^2. Consider a physical target rho(P,w) with P>=r, w>=0, w^2<=P(1-P), and impose

    t=(q(1-P)+cw)/D^2 <= 1.

Then the exact trace error over all finite LOSR outputs is

    delta = 2 max{0, (qw-c(1-P))/D}.

Proof. R*>=1/2, Q*>0. Put a=D^2/q. The source equals a sigma_R*+(1-a)|00><00|, where sigma_R* is the pure MC state with populations R*,Q*. Indeed aQ*=q and a sqrt(R*Q*)=c; a<=1 follows c^2<=rq. For u=(1+sqrt(R*))/2, let H=2|psi_u><psi_u|-I. The all-product-CPTP support result of §53 gives Tr H Lambda(sigma_R*)<=sqrt(R*) for every LOSR map Lambda. A product source can only yield separable outputs, and their overlap with psi_u is at most its largest Schmidt weight u, so the same bound holds for Lambda(|00><00|). By the source decomposition it holds for Lambda(rho). The MC block of H is [[c/D,q/D],[q/D,-c/D]], with -I on the remaining two basis vectors. Its operator norm is1. Hence trace-norm duality gives

    ||tau-Lambda(rho)||_1 >= Tr H tau-c/D
                              =2(qw-c(1-P))/D.

If qw<=c(1-P), put z=w/c. Then z<= (1-P)/q<=1 and the exact target is

    z rho + [P-zr]|00><00| + [(1-P)-zq]|11><11|.

All coefficients are nonnegative: the last by hypothesis, and P-zr>=P-r(1-P)/q=(P-r)/q>=0. They sum1, giving three product-CPTP branches.

If qw>c(1-P), t>0 and the imposed t<=1 makes omega=t rho+(1-t)|00><00| attainable with two product-CPTP branches. Set b=(qw-c(1-P))/D>0. The MC block of tau-omega is

    b [[c/D,q/D],[q/D,-c/D]],

as follows by inserting t into its diagonal tq-(1-P) and offdiagonal w-tc. This matrix has eigenvalues +/-b, giving norm2b and matching the unrestricted-output lower bound.

At c=q the witness becomes the Bell-source witness, and a=2q<=1. At c=sqrt(rq), the source is pure and this specializes to the section53 result subject to the stated projection condition. For c<q the reduction R*>=1/2 fails, so this proof makes no claim. For t>1, the proposed mixture is invalid and no exact error formula is asserted. General target phases and reversed target/source populations are handled only by the appropriate local unitary reductions; the displayed theorem is for sorted coordinates.

This is a direct quantitative consumer of the all-output pure-source support theorem. It does not establish the complete mixed-source error landscape, a coherent multisector channel optimum, or novelty of its ingredients.

### 55.2 Explicit mixed-source example

Take r=3/4, c=3/10, P=17/20 and w=1/4. The source is strictly mixed since c²=9/100<3/16=r(1−r), and the target is physical since w²=1/16<51/400=P(1−P). Here q=1/4, D=√61/20, c≥q, P≥r and t=45/61<1. Also qw−c(1−P)=7/400>0. Thus the exact unhalved trace error is 7/(10√61), attained by (45/61)ρ+(16/61)|00⟩⟨00|. The target population lies outside the source interval [1/4,3/4].

## 56. Complete trace-error landscape for mixed sources with c >= 1-r

This extends §55 by resolving its remaining corner regime.

Let rho=r|00><00|+q|11><11|+c(|00><11|+|11><00|), with r>=1/2, q=1-r>0 and q<=c<=sqrt(rq). Define D=sqrt(c^2+q^2). For target tau=rho(P,w), after independent local output phase and population sorting assume P>=1/2, w>=0 and w^2<=P(1-P). LOSR is finite convex mixtures of product qubit CPTP maps. The norm below is the unhalved trace norm, with no support restriction on candidate outputs.

The exact error is:

1. If P<=r: delta=2 max(0,w-c), by the population-interval theorem §51.
2. If P>=r and t=[q(1-P)+cw]/D^2<=1: delta=2 max(0,[qw-c(1-P)]/D), by the edge theorem §55.
3. If P>=r and t>=1: delta=2 sqrt((P-r)^2+(w-c)^2).

On overlaps the formulas agree. For t=1, the edge projection equals rho, and its norm difference is the third formula. At P=r, t>=1 is equivalent to w>=c, agreeing with regime1. The product source q=0 is outside these parameters and is already handled by §53.

### 56.1 Full pure-target fidelity support

For u in [1/2,1], define psi_u=sqrt(u)|00>+sqrt(1-u)|11> and f(u)=r u+q(1-u)+2c sqrt(u(1-u)). Then

    sup_Lambda <psi_u|Lambda(rho)|psi_u> = max{u,f(u)}.

Proof. Set R*=c^2/D^2>=1/2, Q*=q^2/D^2, and a=D^2/q<=1. As in §55, rho=a sigma_R*+(1-a)|00><00|. For every LOSR Lambda, §53 bounds the pure-source term by max{u,F(u)}, where F(u)=(sqrt(R*u)+sqrt(Q*(1-u)))^2. The product-source term is at most u by the largest Schmidt probability of psi_u. Therefore its total is at most

    a max{u,F(u)}+(1-a)u = max{u,aF(u)+(1-a)u} = max{u,f(u)}.

The final identity uses aR*+(1-a)=r, aQ*=q and a sqrt(R*Q*)=c. Identity achieves f(u), while simultaneous local reset achieves u. Thus the bound is exact for unrestricted outputs. This argument uses a source decomposition only to establish a bound on one common channel; it does not implement channels conditioned on an unknown decomposition label.

Writing x=2u-1 in [0,1] and y=2sqrt(u(1-u))=sqrt(1-x^2), one has f(u)-u=cy-qx. Hence identity is optimal whenever x/y<=c/q (with the endpoint interpreted directly).

### 56.2 Corner proof

Let A=P-r>=0 and B=w-c. The condition t>=1 is equivalent to cB>=qA. Thus B>=0. If A=B=0, identity gives zero. Otherwise put L=sqrt(A^2+B^2)>0, x=A/L and y=B/L. In fact B>0, since q>0 and cB>=qA. Then x/y=A/B<=c/q. Choose u=(1+x)/2, so y=2sqrt(u(1-u)). For H=2|psi_u><psi_u|-I, the MC block is [[x,y],[y,-x]], the other block is -I, and ||H||_infty=1.

The support result and cy>=qx show that every output xi obeys Tr H xi<=Tr H rho. Therefore

    ||tau-xi||_1 >= Tr H(tau-rho) = 2(xA+yB) = 2L.

Identity attains this bound because tau-rho has MC block [[A,B],[B,-A]], eigenvalues +/-L, and zero other block. This proves the third regime without any MC-output ansatz.

### 56.3 Scope and relation to previous results

This gives all physical MC targets for the entire two-parameter source region q<=c<=sqrt(rq), including strictly mixed sources. It completes the missing t>1 part of §55 by a family of supporting witnesses, and reuses §51 for the central population interval. Sources with 0<=c<q remain outside the support derivation and their general positive-error optimum is not asserted. No general coherent multisector RT optimum follows from this state theorem. The proof uses §53's standard Schmidt support method; no novelty claim is made for that ingredient, the PIO construction, or convex support identities.

For a strictly mixed corner example take r=3/4, c=3/10, P=4/5 and w=2/5. The source determinant is 39/400>0, while the target is physical and pure. Then t=68/61>1, P−r=1/20 and w−c=1/10, so the exact unhalved trace error is √5/10, attained by identity. This example lies outside the §55 projection regime.

## 57. Complete mixed-MC source to MC target trace-error formula

All norms below are unhalved Schatten trace norms. LOSR means finite convex mixtures of product qubit CPTP maps, with arbitrary local product ancillas, no additional entanglement, communication or postselection. Competitor outputs are unrestricted two-qubit states.

By independent local input and output unitaries, write the source as rho=r|00><00|+q|11><11|+c(|00><11|+|11><00|), where r>=1/2, q=1-r and 0<=c<=sqrt(rq); write the target as tau=P|00><00|+(1-P)|11><11|+w(|00><11|+|11><00|), where P>=1/2, 0<=w<=sqrt(P(1-P)). These reductions preserve the allowed set and trace distance.

If q=0, the exact error is 2w. If q>0, put D=sqrt(q^2+c^2) and t=[q(1-P)+cw]/D^2. The exact error is

    2 max(0,w-c),                         P<=r;
    2 max(0,[qw-c(1-P)]/D),               P>=r and t<=1;
    2 sqrt((P-r)^2+(w-c)^2),              P>=r and t>=1.

The formulas agree on overlaps. The first regime reuses §51. The last two remove the source condition c>=q from §§55–56. In particular the theorem includes every physical mixed MC qubit source and target. It makes no statement about non-MC targets or coherent multisector recovery channels.

### 57.1 Unrestricted pure-target fidelity support

For u in [1/2,1], let psi_u=sqrt(u)|00>+sqrt(1-u)|11>, and f_r,c(u)=ru+q(1-u)+2c sqrt(u(1-u)). We prove

    sup_Lambda <psi_u|Lambda(rho)|psi_u> = max{u,f_r,c(u)}.

The fidelity convention is the displayed squared overlap. Identity and simultaneous product reset attain the two quantities. The issue is the upper bound for all product CPTP maps, including nonunital maps and outputs outside MC support.

**Reduction to a channel paired with its conjugate.**

For channel A define A_kl,ij=<k|A(|i><j|)|l>, and similarly B. Put rho_00=r, rho_11=q, rho_01=rho_10=c and s_kl=sqrt(u_k u_l), where u_0=u,u_1=1-u. Every weight rho_ij s_kl is nonnegative. The fidelity is

    F(A,B)=sum_{i,j,k,l} rho_ij s_kl A_kl,ij B_kl,ij.

Weighted Cauchy–Schwarz implies F(A,B)<=sqrt(Q(A)Q(B)), where Q(A)=sum rho_ij s_kl |A_kl,ij|^2. Entrywise conjugation of all Kraus matrices produces a CPTP channel conjugate(A) whose coefficients are conjugates of A's, and Q(A)=F(A,conjugate(A)). Compactness therefore gives max_A,B F(A,B)=max_A Q(A). Affinity extends this to finite LOSR mixtures. This reduction concerns fidelity support, not a direct restriction on trace-distance optimizers.

**Balanced-source boundary.**

Fix x in [0,1/sqrt(2)], y=sqrt(1-x^2)>0, k=x/y in [0,1], and u=(1+x)/2. Consider the balanced source r=q=1/2,c=k/2. We prove Q(A)<=u for every qubit CPTP map.

Order the Choi matrix by input index first, then output index, and write

    J_A = [[a, h, s, z],
           [conj(h), 1-a, v, -s],
           [conj(s), conj(v), b, l],
           [conj(z), -conj(s), conj(l), 1-b]].

This is the general Hermitian Choi form after the trace-preserving constraints: a,b are real in [0,1], the diagonal blocks each have trace1, and the off-diagonal block has trace0. Positivity of its 2-by-2 principal minors gives

    |h|^2+|l|^2 <= a(1-a)+b(1-b),
    |z|^2+|v|^2 <= a(1-b)+(1-a)b,
    |s|^2 <= min{ab,(1-a)(1-b)}.

Direct substitution in Q, using 2sqrt(u(1-u))=y and ky=x, yields

    2Q = a^2+b^2-(1-x)(a+b)+(1-x)
         +y(|h|^2+|l|^2)+2k|s|^2+x(|z|^2+|v|^2).

Set S=a+b, V=ab and L=1-y+x-k=(1-y)(1-k)>=0. The principal-minor bounds imply

    2u-2Q >= 2x+(1-2x-y)S-(1-y)S^2
               +2(1-y+x)V-2k min{V,1-S+V}.

If S<=1, the minimum is V and V>=0. Thus the right side is at least

    2x+(1-2x-y)S-(1-y)S^2
      =(1-S)[2x+(1-y)S]>=0.

If S>=1, the minimum is 1-S+V and V>=S-1, since (1-a)(1-b)>=0. The coefficient of V after combining terms is 2L>=0. Substitution of V>=S-1 simplifies the lower bound to

    (1-y)(S-1)(2-S)>=0.

Here 0<=S<=2. Both cases prove Q<=u, including all endpoints. Identity also attains u on this boundary because c y=q x. This proof covers every Choi rank and every local environment.

**Convex completion over all source parameters.**

For fixed u<1 write x=2u-1, y=2sqrt(u(1-u))>0, k=x/y. The physical sorted source domain is the closed quarter-disk

    D_source={(r,c): 1/2<=r<=1, c>=0, c^2<=r(1-r)}.

Split it by the line c=k(1-r). On the lower region f_r,c(u)<=u; on the upper region f_r,c(u)>=u. For each fixed product channel, its fidelity is affine in (r,c). On each of the two compact convex regions the proposed upper bound (u or f_r,c(u)) is also affine. It therefore suffices to establish the bound at that region's extreme points.

The boundary consists of a circular arc, the segments r=1/2 and c=0, and the splitting line. An extreme point is consequently either on the circular arc, one of (1/2,0),(1,0), or the intersection (1/2,k/2) when 0<=k<=1. Intersections of the splitting line with the circular arc are already included in the first category; interior points of any straight boundary segment are not additional extreme points. The circular arc consists of pure MC sources, for which the all-output fidelity bound is §53. The classical corners have bound u by separability (and (1,0) has f=u). The only remaining point is exactly the balanced-source boundary proved above. If k>1, this point is outside the domain and is not needed. Thus the bound holds throughout both regions, and hence for every source. At u=1 the bound is simply1 and reset attains it. This proves the support identity.

### 57.2 Trace-norm lower bounds and explicit attainers

For P<=r the population-interval theorem §51 applies. Suppose P>=r and q>0. Use x=c/D,y=q/D and u=(1+x)/2. Then c y=q x, so the support identity shows that H=2|psi_u><psi_u|-I has output support at most x. Its MC block is [[x,y],[y,-x]] and its other block is -I. Norm duality gives the all-output lower bound

    ||tau-Lambda(rho)||_1 >= 2[qw-c(1-P)]/D.

If qw<=c(1-P) and c>0, z=w/c gives the exact attainable target

    tau=z rho+[P-zr]|00><00|+[(1-P)-zq]|11><11|.

The weights are nonnegative because z<=(1-P)/q<=1 and P-zr>=(P-r)/q>=0. If c=0 the same zero-error condition forces w=0, and the target is a mixture of the two resets. Thus zero error is attained in every zero-bound case.

If qw>c(1-P) and t<=1, t>0 and omega=t rho+(1-t)|00><00| is attainable. Its residual MC block is

    b [[c/D,q/D],[q/D,-c/D]],  b=[qw-c(1-P)]/D>0.

It has eigenvalues +/-b and hence trace norm2b. This also applies when c=0 and w>0. The other block vanishes.

For t>=1 put A=P-r>=0 and B=w-c. The condition is equivalent to cB>=qA. If c>0 it gives B>=0; apart from A=B=0 one has B>0. Set L0=sqrt(A^2+B^2), x=A/L0,y=B/L0 and u=(1+x)/2. Then cy>=qx, so the support identity gives Tr H xi<=Tr H rho for every output xi. Norm duality gives ||tau-xi||_1>=2(xA+yB)=2L0. Identity attains this since tau-rho has MC eigenvalues +/-L0. If c=0, t>=1 and P>=r imply P=r; §51 gives2w, which agrees with the corner formula. The zero residual is immediate. Finally q=0 forces c=0; separability/negativity yields the lower bound2w and the population-matching mixture of product resets attains it.

At t=1, the edge attainer equals rho and its norm is exactly the corner expression. At P=r, t<=1 means w<=c when c>0, and both formulas vanish; t>=1 gives2(w-c), matching §51. The c=0 overlaps were treated explicitly. Thus every physical source/target parameter and all degeneracies are covered, with at most three product-CPTP branches overall.

### 57.3 Scope and attribution

The exact zero-error region agrees with the PIO reachable geometry and the independently proved full-support necessity in §54; that geometry and its construction are not claimed as new. The pure-source boundary uses §53's explicit Schmidt-support proof, following the standard method of George–Chitambar, Phys. Rev. A109,062418 (2024), https://link.aps.org/accepted/10.1103/PhysRevA.109.062418 . PIO predecessors are Shi et al., Scientific Reports7,14806 (2017), https://www.nature.com/articles/s41598-017-13687-4 , and Chitambar–Gour, Phys. Rev. A94,052336 (2016), https://link.aps.org/accepted/10.1103/PhysRevA.94.052336 . No literature priority claim is made for the auxiliary Cauchy–Schwarz, Choi-minor or convexity arguments. The conclusion is the complete all-output trace-norm optimum on the physical two-qubit MC source/target family, not the original coherent multisector RT optimum.

For an explicit low-coherence example, take r=3/4, c=1/10 and the pure target P=9/10, w=3/10. Here q=1/4>c, D=√29/20 and t=22/29. The exact error is 13/(5√29), attained by (22/29)ρ+(7/29)|00⟩⟨00|. This lies outside the source region of §56 and exceeds the negativity lower bound 2(w−c)=2/5.

## 58. Exact common-channel obstruction for encoded amplitude damping

This is a coherent logical-channel problem with arbitrary reference inputs, not a collection of independently optimized state conversions.

### 58.1 Model and theorem

Let L=C² be the logical input, and X=Y=C² the two physical local systems. Define V:L->X tensor Y by V|0>=|00>, V|1>=|11>, and J(Z)=VZV*. For t in [0,1], let D_t be the logical amplitude-damping channel with Kraus matrices K_0=|0><0|+sqrt(t)|1><1| and K_1=sqrt(1-t)|0><1|. The target channel is T_t=J composed with D_t, from L to X tensor Y.

Competitors are F=Phi composed with J, where Phi is any finite convex mixture of product qubit CPTP maps A tensor B. Local product ancillas are allowed; communication, postselection, and additional shared entanglement are not. Neither code-support preservation nor exact action on either basis state is imposed. Diamond norm includes arbitrary passive references and is not divided by two.

Then

    inf_Phi ||Phi composed with J - T_t||_diamond
       = (8/9)(sqrt(t)-t).

The infimum is attained by two product-CPTP branches: with probability a=(2t+sqrt(t))/3 use identity on both physical systems, and with probability 1-a reset both to |0>. The same random choice and same physical channel act on every logical input. At t=0 or t=1, a single branch suffices.

### 58.2 Unrestricted all-product lower bound

Use the fixed reference input Omega=sqrt(1/3)|0>_R|0>_L+sqrt(2/3)|1>_R|1>_L. On R tensor X tensor Y define the Hermitian witness H as follows. On the span of |0,00>,|1,11> its matrix is

    [[1/3,2sqrt(2)/3],[2sqrt(2)/3,-1/3]].

On |1,00> it is +1; on each of the other five computational basis vectors it is -1. The displayed block squares to identity, so ||H||_infty=1.

For an arbitrary product channel A tensor B put

    a0=<0|A(|0><0|)|0>, b0=<0|B(|0><0|)|0>,
    a1=<1|A(|1><1|)|1>, b1=<1|B(|1><1|)|1>,
    z_A=<0|A(|0><1|)|1>, z_B=<0|B(|0><1|)|1>.

All four probabilities lie in [0,1]. Complete positivity, through a two-by-two Choi principal minor, gives |z_A|<=sqrt(a0 a1) and |z_B|<=sqrt(b0 b1). Directly expanding the reference output sigma=(id_R tensor [(A tensor B) composed with J])(|Omega><Omega|) gives

    9 Tr(H sigma)
      =4a0b0+12(1-a1)(1-b1)+4a1b1+8 Re(z_A z_B)-9.

For example, the R=0 diagonal contribution is (4a0b0-3)/9; the R=1 contribution is [12(1-a1)(1-b1)+4a1b1-6]/9; and the two coherent terms give 8 Re(z_A z_B)/9. Thus leakage outside the code is included explicitly, not discarded.

Put z=sqrt(a1b1). The nonconstant part of the preceding expression is at most

    4[(sqrt(a0b0)+z)^2+3(1-a1)(1-b1)]
      <=4[(1+z)^2+3(1-z)^2]
      =16(1-z+z^2)<=16.

Here a0b0<=1, and a1+b1>=2sqrt(a1b1) proves (1-a1)(1-b1)<=(1-z)^2. Finally 0<=z<=1. Consequently Tr(H sigma)<=7/9 for every product channel, and affinity gives the same bound for every finite LOSR mixture. The argument uses no code-support or calibration assumption.

The ideal reference output has weights 1/3 on |0,00>, 2t/3 on |1,11>, 2(1-t)/3 on |1,00>, and coherent matrix entry sqrt(2t)/3 between the first two vectors. Therefore

    Tr[H (id_R tensor T_t)(|Omega><Omega|)]
      =7/9+(8/9)(sqrt(t)-t).

Trace-norm duality with ||H||_infty=1 yields the claimed diamond lower bound. The one fixed input and witness apply to the whole allowed physical class.

### 58.3 One common physical attainer and its full diamond norm

Put k=sqrt(t)-t>=0, a=t+k/3=(2t+sqrt(t))/3. Since 0<=t<=sqrt(t)<=1, a lies in [0,1]. The two-branch physical channel above has encoded action

    F_a(Z)=a VZV*+(1-a)Tr(Z)|00><00|.

Its difference from the target has population mismatch d=a-t=k/3 and coherence mismatch e=sqrt(t)-a=2k/3. In the code basis, Delta=T_t-F_a acts by

    Delta(|0><0|)=0,
    Delta(|1><1|)=d(|00><00|-|11><11|),
    Delta(|0><1|)=e|00><11|,
    Delta(|1><0|)=e|11><00|.

Let an arbitrary normalized pure input with any reference be |0>u+|1>v, where ||u||²=1-q, ||v||²=q and 0<=q<=1. Its output difference is the sum of the positive rank-one term d|00><00| tensor |v><v| and an operator supported on the orthogonal vectors |00>u, |11>v. The latter has matrix

    [[0,e sqrt(q(1-q))],[e sqrt(q(1-q)),-dq]]

in their normalized basis, with the zero-vector endpoints interpreted by continuity. Its trace norm is sqrt(d²q²+4e²q(1-q)). The triangle inequality therefore gives

    ||(Delta tensor id)(|Psi><Psi|)||_1
      <=dq+sqrt(d²q²+4e²q(1-q))
      =(k/3)[q+sqrt(16q-15q²)] <= 8k/9.

The final inequality follows by squaring the nonnegative right side of sqrt(16q-15q²)<=8/3-q: the difference of the two squares is 16(q-2/3)². Equality occurs at q=2/3, with u and v orthogonal. In that case the positive rank-one term is orthogonal to the two-dimensional block, so the triangle inequality is also equality. This is exactly the reference input Omega used above.

Mixed density inputs follow by convexity. To cover arbitrary trace-class operator inputs in the diamond norm, first use the Jordan decomposition for Hermitian inputs. For a general operator Z, add a reference qubit and use the Hermitian block operator (1/2)[[0,Z],[Z*,0]], whose trace norm is ||Z||_1 and whose image has trace norm ||(Delta tensor id)(Z)||_1. Since Delta preserves Hermiticity, the density-input bound thus applies to all operators and arbitrary finite references. This proves the exact diamond norm and attainment.

### 58.4 Compatibility consequence and scope

Both logical basis targets are individually exactly attainable: |00> remains |00>, and |11> can be sent to (1-t)|00><00|+t|11><11| by shared random resets. In fact one common identity/reset mixture with weight t matches both basis outputs simultaneously. It multiplies the logical off-diagonal by t, whereas T_t requires sqrt(t). For 0<t<1 the theorem proves that no alternative physical finite-LOSR channel can remove this coherent discrepancy completely, even by allowing leakage or changing the basis outputs. The actual optimum accepts a small population error, choosing a=(2t+sqrt(t))/3 rather than t.

For t=1/4 the exact unhalved diamond error is 2/9 and the optimal identity weight is 1/3. Thus this is a strict common-channel obstruction even though separate basis-state conversion errors vanish. It complements §54's exact-support channel normal form, but its lower bound is stronger in scope because competitors here need not preserve the code. It does not rely on optimizing sector states independently and identifying those optimizers with a channel.

Sections 38–39 give common coherent implementations with isometric pure flat-sector targets; Sections 40–44 develop restricted-control and Schur-channel statements. The target here is a nonunital logical noise channel with mixed basis output, not a pure flat-target encoding isometry, so those formulas do not directly supply this value. Section 57 gives exact MC state-conversion errors but does not itself optimize this reference-sensitive common-channel task. The present two-label model is a concrete coherent consumer, not a proof of general RT recovery or a gravitational dictionary.

Amplitude damping, Choi positivity, trace-norm duality and diamond norm are standard. A primary background reference is Watrous, The Theory of Quantum Information (2018), §3.3, Definition 3.43 and Theorem 3.51, https://cs.uwaterloo.ca/~watrous/TQI/ . No literature-priority claim is made for these ingredients or for a general nonlocal-channel classification. The precise result established here is the stated finite-LOSR diamond optimum and its explicit physical attainer.

## 59. Exact coherent LOSR projection for all phase-covariant qubit channels

### 59.1 Model and theorem

Let L=X=Y=C², V|0>=|00>, V|1>=|11>, and J(Z)=VZV*. A logical phase-covariant channel E_(α,β,λ) is specified on matrix units by

    E(00)=α00+(1−α)11,
    E(11)=(1−β)00+β11,
    E(01)=λ01, E(10)=conj(λ)10.

Here ij abbreviates |i><j| on the logical system. Its complete positivity and trace preservation are equivalent to 0≤α,β≤1 and |λ|²≤αβ: its input-first Choi matrix has the block [[α,λ],[conj(λ),β]] on |00>,|11> and remaining diagonal entries 1−α,1−β. The parameterization includes every qubit channel covariant under all rotations diag(1,exp(iθ)); covariance forces the displayed matrix-unit form.

Physical competitors are all finite LOSR channels Φ=Σ_b p_b A_b⊗B_b with arbitrary qubit CPTP local maps. Their comparison domain is the logical qubit, via F=Φ∘J, and their output is X⊗Y. Local product ancillas are allowed. Neither code preservation nor phase covariance nor exact basis-state action is imposed on the competitors. The diamond norm is unhalved and includes arbitrary passive references.

Writing c=|λ| and m=min(α,β), the exact optimum is

    inf_Φ ||Φ∘J − J∘E_(α,β,λ)||_diamond = (8/9) max(0,c−m).

One common physical channel attains the optimum on the entire logical operator algebra. At most four product-CPTP branches suffice when the error is zero, and at most three suffice when it is positive. In particular, exact physical implementation is possible if and only if c≤min(α,β). The positive-error lower bound applies to all physical outputs, including leakage outside span{|00>,|11>}.

### 59.2 Exact feasible class and finite common implementations

First assume α≥β and phase-align λ=c≥0. The general case follows by local output phase unitaries and simultaneous logical input/output flips: J intertwines the logical flip with X⊗X, and those pre/post operations preserve the finite physical LOSR class and diamond norm. Simultaneous flips exchange α,β and conjugate λ.

For completeness, §54's full-support channel normal form supplies a direct necessity proof for exact implementation. Apply it to J(I/2), which is strictly positive on the two-dimensional MC code. If Φ∘J=J∘E, every positive-weight product branch preserves that code on all matrix units. Such a branch has a deterministic label map f:{0,1}→{0,1}. Constant f kills the off-diagonal; the flip f sends |00><11| to a multiple of |11><00|; only the identity f contributes to the coefficient of |00><11|. Each such coefficient has modulus at most one. If their total probability is a, then c≤a, while both survival probabilities α and β are at least a. Hence c≤min(α,β). This is an equality of channel actions, not merely a statement about one source state.

Here is an explicit converse using one common random branch. Let I be identity on both physical systems; let R0 reset both to |0>; let Cid=Δ⊗Δ, where Δ is computational-basis dephasing; and let Cflip=(Ad_X∘Δ)⊗(Ad_X∘Δ). Both classical branches erase every off-diagonal code matrix unit. If c≤β≤α, use weights

    c I + (1−α) Cflip + (α−β) R0 + (β−c) Cid.

They are nonnegative and sum to one. On 00 and 11 they give precisely the displayed populations, and on 01 they give c01. Thus all matrix units, and consequently all reference-extended inputs, agree. A local output diagonal unitary restores the desired phase of λ. Zero weights may be omitted. This construction also proves the endpoint cases, including c=0 and α or β equal to zero or one. The necessity above is a consumer of §54, not a new claim of priority for PIO-type channel constructions.

### 59.3 An unrestricted product-channel witness

Continue with α≥β and λ=c≥0. Use the fixed logical-reference input

    |Ω>=sqrt(1/3)|0_R0_L>+sqrt(2/3)|1_R1_L>.

The reference has dimension two and the joint output space R⊗X⊗Y has dimension eight. Define H by the block

    [[1/3,2sqrt(2)/3],[2sqrt(2)/3,−1/3]]

on |0,00>,|1,11>; set H=+1 on |1,00>, H=+1/3 on |0,11>, and H=−1 on each of the remaining four computational basis vectors. The block squares to identity, so ||H||∞=1. The changed value on |0,11>, compared with §58, is essential: it treats both possible code outputs of logical input 0 equally.

For an arbitrary product channel A⊗B put a0=<0|A(00)|0>, b0=<0|B(00)|0>, a1=<1|A(11)|1>, b1=<1|B(11)|1>, and z_A=<0|A(01)|1>, z_B=<0|B(01)|1>. Complete positivity gives |z_A|≤sqrt(a0a1), |z_B|≤sqrt(b0b1). All four probabilities belong to [0,1]. Define

    U=a0b0+(1−a0)(1−b0), B0=(1−a1)(1−b1), C=a1b1.

Expanding σ=(id_R⊗[(A⊗B)∘J])(|Ω><Ω|) gives

    9 Tr(Hσ)=4U+12B0+4C+8 Re(z_A z_B)−9.

Indeed the R=0 diagonal contribution is (4U−3)/9, the R=1 contribution is (12B0+4C−6)/9, and the two coherent contributions total 8 Re(z_A z_B)/9. This expansion retains all leakage probabilities. Now U≤1, a0b0≤1, and with z=sqrt(C) the arithmetic-geometric mean inequality gives B0≤(1−z)². Hence

    4U+12B0+4C+8 Re(z_A z_B)
      ≤4[1+3(1−z)²+z²+2z]
      =16(1−z+z²)≤16.

Thus Tr(Hσ)≤7/9 for every product CPTP map, and by affinity for every finite LOSR mixture. No support-preservation or phase-covariance assumption was used.

For the ideal output, the R=0 populations α/3 and (1−α)/3 both encounter witness value 1/3. The R=1 populations are 2(1−β)/3 on |1,00> and 2β/3 on |1,11>, and the coherent entry is sqrt(2)c/3. Consequently

    Tr[H(id_R⊗J∘E)(|Ω><Ω|)] = 7/9 + (8/9)(c−β).

Trace-norm duality proves the lower bound (8/9)(c−β) when c>β. Nonnegativity gives the zero lower bound otherwise. This holds against every common physical LOSR channel, including ones that alter the populations or leak outside the code.

### 59.4 Exact projection and diamond upper bound

Suppose c>β and α≥β. Put k=c−β>0 and a=β+k/3=(2β+c)/3. Complete positivity gives c≤sqrt(αβ)≤α, so β<a≤α≤1. Choose the exact feasible logical channel E' with parameters (α,a,a), implemented physically by

    a I + (1−α) Cflip + (α−a) R0.

These three weights are nonnegative and sum to one. Thus this is an actual common physical channel, not independently selected state optimizers. The logical output phase can again be restored at the end.

For Δ=J∘(E−E'), the only nonzero matrix-unit differences are

    Δ(11)=(k/3)(|00><00|−|11><11|),
    Δ(01)=(2k/3)|00><11|, Δ(10)=Δ(01)*,

while Δ(00)=0. To verify its full diamond norm, let an arbitrary normalized pure input with any reference be |0>u+|1>v with ||u||²=1−q and ||v||²=q. Write d=k/3 and e=2k/3. The output difference is the positive rank-one operator d|00><00|⊗|v><v| plus a block on the orthogonal vectors |00>u,|11>v with normalized matrix [[0,e sqrt(q(1−q))],[e sqrt(q(1−q)),−dq]]. Therefore its trace norm is at most

    dq+sqrt(d²q²+4e²q(1−q))
      =(k/3)[q+sqrt(16q−15q²)]≤8k/9.

The last inequality follows by squaring sqrt(16q−15q²)≤8/3−q; the difference of the squares is 16(q−2/3)². At q=2/3 with u⊥v, the positive rank-one term is orthogonal to the block and equality holds. This is the same Ω as in the witness proof.

Mixed density inputs follow by convexity. Hermitian operator inputs follow by Jordan decomposition; arbitrary operator inputs follow by adjoining a reference qubit and applying the Hermitian bound to (1/2)[[0,Z],[Z*,0]], whose input and image trace norms equal those of Z and its image. Thus the bound covers the diamond norm, not only unreferenced states. This proves the upper bound and exact attainment. If c≤β, the exact implementation already gives error zero. Local phase unitaries and simultaneous flips give all parameters in the theorem.

### 59.5 Damping, dephasing, and thermal specialization

The damping/dephasing family fixes α=1, β=t and allows |λ|≤sqrt(t). Its exact error is (8/9)max(0,|λ|−t), with §58 recovered at λ=sqrt(t). This is a corollary of the full channel theorem, rather than a separate mathematical increment.

For generalized amplitude damping followed by dephasing, let t∈[0,1], g∈[0,1] be the ground-state equilibrium population, and ζ∈[0,1] the coherence attenuation. The parameters are

    α=g+(1−g)t, β=(1−g)+gt, c=ζ sqrt(t).

They are physical because αβ=t+g(1−g)(1−t)²≥t≥c². The exact unrestricted physical-LOSR error is

    (8/9) max(0, ζ sqrt(t) − [min(g,1−g)+max(g,1−g)t]).

Thus sufficient dephasing gives exact common implementation, while the positive branch is attained by the three physical branches above after the appropriate flip. At thermal balance g=1/2, (1+t)/2≥sqrt(t), so the entire family is exactly implementable. Away from balance it may have a strict obstruction. For example g=9/10,t=1/4,ζ=1 gives α=37/40,β=13/40,c=1/2 and exact error 7/45. The optimal logical parameters are (37/40,23/60,23/60), physically implemented with identity weight 23/60, classical flip weight3/40 and reset-to-zero weight13/24. Both directions of thermal population transfer are present, so this example is not on the reset axis.

### 59.6 Scope and attribution

The result concerns a fixed two-dimensional MC encoding and a whole family of coherent logical channels; all inputs share one physical LOSR implementation. The exact feasible-class argument reuses §54. The zero-temperature boundary reuses §58, while the modified witness establishes the all-output projection off that boundary. Sections38–39 concern isometric flat-sector targets, Sections40–44 restricted-control and Schur results, and §57 optimizes a single MC state pair. None of those statements alone optimizes this full phase-covariant channel family.

Physically incoherent constructions and their zero-communication lifting to maximally correlated systems are established background: Chitambar–Gour, Phys. Rev. A94,052336 (2016), https://link.aps.org/accepted/10.1103/PhysRevA.94.052336 ; related qubit reachable geometry appears in Shi et al., Scientific Reports7,14806 (2017), https://www.nature.com/articles/s41598-017-13687-4 . Diamond norm and reference-assisted channel discrimination are standard; see Watrous, The Theory of Quantum Information (2018), §3.3, https://cs.uwaterloo.ca/~watrous/TQI/ . No priority claim is made for those ingredients or for the parameterization. The theorem is an exact finite-LOSR diamond projection on the stated fixed-code channel family, not a general RT recovery theorem or a classification of arbitrary logical channels.

## 60. Exact leakage removal and diamond projection for parity-covariant logical channels

### 60.1 Model and conclusions

Fix L=X=Y=C² and the MC encoding V|i>=|ii>, J(T)=VTV*. Write ij=|i><j| on L. Consider

    E(00)=α00+(1−α)11, E(11)=(1−β)00+β11,
    E(01)=λ01+μ10, E(10)=conj(λ)10+conj(μ)01.

These are exactly the qubit channels covariant under conjugation by Z=diag(1,−1). They form a narrower class than channels merely preserving the diagonal algebra, which can also convert off-diagonal input into diagonal output. The necessary and sufficient CPTP conditions are 0≤α,β≤1, |λ|²≤αβ and |μ|²≤(1−α)(1−β), by the two blocks of the input-first Choi matrix.

Physical competitors are finite mixtures Φ=Σ_b p_b A_b⊗B_b of arbitrary local qubit CPTP maps, including local product ancillas. They act on every logical input through Φ∘J. Diamond norm is unhalved and includes arbitrary passive references. No code-preservation or covariance restriction is imposed on these competitors.

The following conclusions hold.

1. Exact physical implementation Φ∘J=J∘E is possible if and only if

       |λ|≤min(α,β), |μ|≤min(1−α,1−β).

   Every channel satisfying these simultaneous conditions has an implementation with at most four product-CPTP branches.
2. For every physical competitor, there is a common physical competitor that preserves the code and is parity-covariant, with no greater diamond error against J∘E. Thus unrestricted leakage cannot improve the optimum anywhere in this family.
3. After phase alignment, the unrestricted optimum equals the explicit finite semidefinite program below. Its optimizer yields the four-branch physical attainer. This is an exact optimization formula for all parameters, including unequal simultaneous deficits; it is not a claimed elementary closed form.
4. In the simultaneous equal-deficit family α≥β, λ,μ≥0 and λ−β=μ−(1−α)=k>0, the exact optimum is sqrt(2)k. A three-branch common physical channel attains it. This differs from treating the two coherence constraints independently.

### 60.2 The exact common-channel feasible class

Put l=|λ|, m=|μ|. Necessity follows from §54's full-support normal form: apply an exact implementation to J(I/2). Every positive-weight product branch has a deterministic code-label map f. Identity f can contribute only to λ, with coefficient of modulus at most one; flip f can contribute only to μ, also with modulus at most one; constant f kills both coherences. If total identity and flip branch weights are a and b, then l≤a≤min(α,β) and m≤b≤min(1−α,1−β).

For a constructive converse set S=1−l−m, A=α−l, B=β−l. The displayed inequalities imply S≥0 and 0≤A,B≤S. Choose U=max(0,A+B−S), so 0≤U≤min(A,B). Define

    wI=l+U, wF=m+S−A−B+U, w0=A−U, w1=B−U.

All weights are nonnegative and sum to one. Use an identity-label branch of weight wI, with local dephasing on Alice chosen so its logical 01 coefficient is λ/wI. Use a flip-label branch of weight wF: dephase Alice and then apply X on both sides, choosing the dephasing coefficient so the resulting logical 10 coefficient is μ/wF. Local dephasing with any complex multiplier of modulus at most one is CPTP. The remaining branches reset both parties to |0> or |1>, with weights w0,w1. Zero-weight branches are omitted, so division by zero is never needed. The identity and flip weights dominate l and m respectively. Directly on the four matrix units, the resulting channel has populations α=wI+w0, β=wI+w1 and coherences λ,μ. Therefore it agrees on all logical inputs and all reference extensions. This reuses the known PIO-type constructions; no new priority is asserted for the feasible-class ingredients.

### 60.3 A contractive global retraction with a separately physical output implementation

Let P=|00><00|+|11><11| and Q=I−P on X⊗Y, and set ω=(|00><00|+|11><11|)/2. Define the global CPTP map

    R(T)=PTP+Tr(QT)ω.

Complete positivity follows, for example, from Kraus operator P and the four operators |ii><jk|/sqrt(2), with i∈{0,1} and jk∈{01,10}; their adjoint products sum to P+Q=I. The map fixes every code-supported operator and kills code/leak cross terms. It is used only as a mathematical contraction, not claimed to be an LOSR operation.

Let U=Z⊗I on the physical output. For any physical Φ define the two-term physical twirl

    Φbar=(Φ+Ad_U∘Φ∘Ad_U)/2.

This remains finite LOSR, since U is local, and U V=V Z. The target J∘E is fixed by the corresponding input/output symmetry. Unitary invariance and convexity of diamond norm give ||Φbar∘J−J∘E||diamond≤||Φ∘J−J∘E||diamond. The map R commutes with Ad_U, so R∘Φbar∘J is a code-supported parity-covariant channel.

Consider one arbitrary product branch A⊗B before this twirl. Put a0=<0|A(00)|0>, a1=<1|A(11)|1>, and b0,b1 similarly. Let z_A=<0|A(01)|1>, v_A=<1|A(01)|0>, with analogous coefficients for B. Choi principal minors give

    |z_A|²≤a0a1, |v_A|²≤(1−a0)(1−a1),

and the same for B. Retraction and twirling give logical parameters

    α'=(a0+b0)/2, β'=(a1+b1)/2,
    λ'=z_A z_B, μ'=v_A v_B.

For example the new 00 probability on input00 is a0b0+[a0(1−b0)+(1−a0)b0]/2=(a0+b0)/2. Twirling removes all diagonal-to-off-diagonal and off-diagonal-to-diagonal coefficients; it preserves the two displayed coherence directions. Moreover

    |λ'|≤sqrt(a0a1b0b1)≤min((a0+b0)/2,(a1+b1)/2),
    |μ'|≤sqrt((1−a0)(1−a1)(1−b0)(1−b1))
         ≤min(1−(a0+b0)/2,1−(a1+b1)/2).

The first line follows by dropping a1b1≤1 and then applying the arithmetic-geometric mean bound, or dropping a0b0≤1; the second is identical with complemented probabilities. For mixtures the same inequalities follow from the triangle inequality and affinity of the populations. Thus R∘Φbar∘J=J∘E' for a channel E' in the exact feasible class above, and that class supplies an actual finite physical implementation Ψ of E'. Complete trace-norm contractivity of R now gives

    ||Ψ∘J−J∘E||diamond
      =||R∘Φbar∘J−R∘J∘E||diamond
      ≤||Φ∘J−J∘E||diamond.

This proves leakage removal for optimization without pretending that R itself is a physical local protocol. Both twirling and retraction act on one common channel, not on separately optimized inputs. Since the feasible parameters form a compact set and diamond norm is continuous, an optimal parameter choice exists and is physically attained by at most four branches.

### 60.4 An explicit exact finite projection program

Independent diagonal input and output unitaries can make λ and μ simultaneously real and nonnegative: for input angle θ and output angle φ their phases change by −θ−φ and −θ+φ, respectively. These logical unitaries lift to local physical unitaries, preserve the allowed class, and preserve diamond distance. Zero coefficients need no phase choice. Hence write the aligned target as (α,β,l,m) with l,m≥0.

For a competitor let a,b be its survival probabilities and x,y its real coherence coefficients. Real coefficients lose no optimality: average a feasible competitor with its entrywise complex conjugate, using that the target is real and diamond norm is invariant under simultaneous input/output complex conjugation. The exact feasible inequalities are

    0≤a,b≤1,
    −a≤x≤a, −b≤x≤b,
    −(1−a)≤y≤1−a, −(1−b)≤y≤1−b.

These linear constraints imply the CPTP inequalities automatically. Define u=α−a, v=β−b and the real symmetric Choi difference blocks

    D1=[[u,l−x],[l−x,v]],
    D2=[[-u,m−y],[m−y,−v]].

The blocks use ordered bases {|0,0>,|1,1>} and {|0,1>,|1,0>} of the logical input/output Choi space. They are unnormalized Choi blocks; no factor1/2 is inserted.

Minimize a real scalar δ over a,b,x,y and real symmetric two-by-two matrices Z1,Z2, subject to the feasible inequalities above and

    Z1−D1≥0, Z1+D1≥0,
    Z2−D2≥0, Z2+D2≥0,
    (Z1)11+(Z2)11≤δ,
    (Z1)22+(Z2)22≤δ.

The minimum equals the unrestricted physical LOSR diamond optimum. To see this, for any Hermiticity-preserving difference map with Choi matrix D, the standard diamond-norm dual is min ||Tr_out Z||∞ over Hermitian Z≥D and Z≥−D. Here the trace bound is exactly Tr_out Z≤δ I. Averaging Z under Z⊗Z makes it block diagonal in the displayed parity blocks; averaging with entrywise conjugation makes it real, without changing feasibility or increasing δ. Partial trace gives precisely the two diagonal sums displayed above. Conversely any listed Z1,Z2 reconstruct a feasible diamond dual. Thus the program is exactly the ordinary diamond dual optimized over the independently established physical feasible class; the retraction theorem proves that no unrestricted leakage competitor was omitted. Feasibility and attainment follow from the compact parameter minimum and the finite-dimensional diamond dual. Each two-by-two positive-semidefinite constraint can equivalently be written as a second-order-cone constraint. No numerical solution is assumed in this theorem, and the general unequal-deficit value is specified by this exact finite program rather than an unproved closed formula.

### 60.5 A sharp simultaneous-deficit family

Assume α≥β, l=β+k and m=1−α+k with k>0, and the physical CPTP inequalities. Cauchy–Schwarz gives l+m≤sqrt(αβ)+sqrt((1−α)(1−β))≤1, so 2k≤α−β. Define

    a=α−k/2, b=β+k/2, x=b, y=1−a.

These are feasible. The corresponding common physical implementation consists of identity on both sides with weight β+k/2, flip X on both with weight1−α+k/2, and simultaneous reset to zero with weight α−β−k. All weights are nonnegative and sum to one. The phase-aligned logical difference Δ=E−E' has

    Δ(00)=Δ(11)=(k/2)Z,
    Δ(01)=Δ(10)=(k/2)X.

Consequently, with P±=(I±X)/2,

    Δ(T)=(k/2)[Tr(P+T)(Z+X)+Tr(P−T)(Z−X)].

For a density input with any reference, its two positive conditional reference operators ρ± have total trace one. Since ||Z±X||1=2sqrt(2), the triangle inequality bounds the output trace norm by sqrt(2)k. Convexity, Jordan decomposition and the Hermitian block embedding used in §58 extend this bound to all operator inputs and hence to diamond norm. Encoding J preserves trace norm, including references.

For a direct lower bound against all physical products, use |Ω>=(|0_R0_L>+|1_R1_L>)/sqrt(2). On the joint output define H=0 outside the reference/code subspace. On |0,00>,|1,11> use [[1,1],[1,−1]]/sqrt(2); on |0,11>,|1,00> use [[−1,1],[1,1]]/sqrt(2). Thus ||H||∞=1. With the product-channel notation above, put t_A=a0−a1 and t_B=b0−b1. Direct expansion gives

    sqrt(2) Tr(Hσ)=(t_A+t_B)/2+Re(z_Az_B+v_Av_B).

The Choi minor bounds imply

    |z_A|²+|v_A|²≤a0a1+(1−a0)(1−a1)≤1−|t_A|,

and similarly for B. The last inequality follows by considering a0≥a1 and a1≥a0 separately; its slack is twice the smaller probability times one minus the larger. Cauchy–Schwarz and the arithmetic-geometric mean inequality therefore bound the displayed witness expectation by 1/sqrt(2). Mixtures obey the same bound. On the ideal output it equals [(α−β)+l+m]/sqrt(2)=(1+2k)/sqrt(2). Norm duality gives the lower bound sqrt(2)k, matching the common physical attainer.

For an explicit genuinely two-direction example take α=4/5, β=1/5 and l=m=2/5. Both Choi determinant bounds are saturated and k=1/5. The exact diamond error is sqrt(2)/5, attained by weights3/10 identity,3/10 simultaneous flip,2/5 simultaneous reset to zero. Applying the one-direction §59 formula separately would give8/45 for each deficit, strictly below the true joint optimum; a maximum of separate errors is not the channel answer.

### 60.6 Attribution and scope

The exact-code branch classification reuses §54 and the PIO-to-zero-communication construction described by Chitambar–Gour, Phys. Rev. A94,052336 (2016), https://link.aps.org/accepted/10.1103/PhysRevA.94.052336 . Standard diamond semidefinite programs are due to Watrous; see Simpler semidefinite programs for completely bounded norms, https://arxiv.org/abs/1207.5726 . Channel-conversion SDPs also occur in dynamical coherence theory, for different free superchannels, in Saxena–Chitambar–Gour, Phys. Rev. Research2,023298 (2020), https://doi.org/10.1103/PhysRevResearch.2.023298 . These constructions and general optimization machinery are not claimed as new. The result here is the proved unrestricted-output reduction for the specified physical LOSR/code model, the resulting exact simultaneous-coherence projection, and the sharp common-channel family above. It does not classify arbitrary diagonal-algebra-preserving channels, all logical channels, or general RT recovery.

## 61. Pairwise coherent implementability does not imply a common qutrit LOSR channel

### 61.1. Fixed-code model and a saturated-path constraint

For d≥2 let L=C^d and X=Y=C^d, with fixed MC encoding V|i>=|ii> and J(T)=VTV*. Physical maps are finite LOSR mixtures Φ=Σ_b w_b A_b⊗B_b of local CPTP maps. One map Φ must act on all logical inputs, including all reference extensions. Suppose Φ∘J has output supported on the MC code for every logical input. Define p_i as the probability of the physical output |ii> on logical input |i><i|, and define λ_ij as the coefficient of |ii><jj| in Φ(J(|i><j|)). Other output matrix-unit coefficients are not assumed absent in this general constraint.

Let i_0,...,i_m be a path of distinct labels with 0<p_i0≤p_i1≤...≤p_im. If for each adjacent pair

    λ_(i_(r−1),i_r)=p_(i_(r−1)) exp(iθ_r),

then a necessary condition for one common physical implementation is

    λ_(i_0,i_m)=p_i0 exp(i(θ_1+...+θ_m)).

This is a dimension-independent compatibility condition on saturated retained coherences. It is stronger than checking each adjacent pair's magnitude separately.

Proof. Apply §54's full-support normal form to J(I/d). Every positive-weight product branch has one deterministic label map f_b and a code action

    |ii><jj| -> C_b,ij |f_b(i)f_b(i)><f_b(j)f_b(j)|,

where C_b is a positive-semidefinite unit-diagonal correlation matrix, the entrywise product of the two local Gram matrices. This positivity also follows directly by using tensor products of their Gram vectors. Let E_i be the event f_b(i)=i under branch weights w_b. Then P(E_i)=p_i and

    λ_ij=E[1_(E_i∩E_j) C_b,ij].

For p_i≤p_j, equality λ_ij=p_i exp(iθ) in the bounds

    |λ_ij|≤E[1_(E_i∩E_j)|C_b,ij|]≤P(E_i∩E_j)≤p_i

forces E_i⊆E_j up to zero-weight branches and C_b,ij=exp(iθ) on E_i. This follows equally by integrating the nonnegative quantity 1−Re(exp(−iθ)C_b,ij) over E_i after the event inclusion has been established. Along the path, E_i0 is contained in every E_ir. On this event all adjacent Gram inner products have unit modulus and the prescribed phase. Equality in Cauchy–Schwarz for unit Gram vectors makes successive vectors proportional, so their endpoint inner product is exp(iΣ_r θ_r). Thus C_b,i0im has that value on E_i0. Since E_i0⊆E_im, the displayed formula for λ gives the conclusion. The unit-Gram-vector step is the usual equality case of Cauchy–Schwarz, not a new correlation-matrix theorem. The use of a single branch space for the entire path is essential.

### 61.2. A continuous qutrit counterexample family with explicit complete positivity

Take d=3, 0<q<1 and 0<p≤q(1−q). Define the logical channel E_(p,q) by

    E(11)=p11+(1−p)33,
    E(22)=q22+(1−q)33,
    E(33)=33,
    E(12)=p12, E(23)=q23, E(13)=0,

and by adjoints on reversed off-diagonal matrix units. Here ij denotes |i><j| on L; the input labels are1,2,3.

This is CPTP. In the input-first Choi matrix, the block on |1,1>,|2,2>,|3,3> is

    K=[[p,p,0],[p,q,q],[0,q,1]],

and the only additional nonzero entries are the nonnegative diagonal entries1−p on |1,3> and1−q on |2,3>. Every principal minor of K is nonnegative: its diagonal entries are p,q,1; its two-by-two principal determinants are p(q−p),p,q(1−q); and its full determinant is p[q(1−q)−p]. Hence K≥0. The displayed diagonal outputs each have trace one and off-diagonal outputs have trace zero, so the map is trace preserving.

At the concrete boundary point p=1/4,q=1/2, complete positivity and trace preservation can also be read directly from four Kraus matrices:

    D1=diag(1/2,1/2,0), D2=diag(0,1/2,1),
    L1=(sqrt(3)/2)|3><1|, L2=(1/sqrt(2))|3><2|.

Their adjoint products sum to identity; their off-diagonal coefficients are1/4 on12,1/2 on23, and0 on13, as required. This example is a genuinely qutrit channel rather than three unrelated prescribed output states.

### 61.3. Every two-label restriction has one finite physical implementation

For each pair {i,j}, restrict the logical input to span{|i>,|j>} while retaining the full qutrit output and the same physical encoding J. Exact implementability means equality of the two channels on that entire two-dimensional input algebra, including its off-diagonal units and all references; it does not require the output to remain within the chosen pair of labels.

Let I denote identity on both physical qutrits and R3 the product channel resetting both to |3>. For a deterministic label function f:{1,2,3}→{1,2,3}, define the local CPTP map M_f(T)=Σ_i <i|T|i>|f(i)><f(i)|. The product M_f⊗M_f destroys every off-diagonal code matrix unit and maps |ii><ii| to |f(i)f(i)><f(i)f(i)|.

The following are three distinct allowed choices of a common physical channel, one for each restriction:

- On {1,2}, use p I+(q−p)(M_f⊗M_f)+(1−q)R3, where f(1)=3,f(2)=2,f(3)=3. The weights are nonnegative because p≤q(1−q)≤q. Input1 has survival p, input2 survival q, and the12 coherence multiplier is p.
- On {2,3}, use q I+(1−q)R3. Input2 has survival q, input3 remains3, and the23 coherence multiplier is q.
- On {1,3}, use p(M_id⊗M_id)+(1−p)R3. Input1 has survival p, input3 remains3, and the13 coherence is killed.

Direct checking of the four matrix units in each restricted algebra proves exact channel equality. By linearity the same equality holds after tensoring with every passive reference. These constructions use at most three product-CPTP branches and act on all coherent inputs of their respective pair; no input-dependent branch selection or postselection is used.

### 61.4. No common full-code implementation exists

Suppose a single finite physical LOSR channel Φ satisfied Φ∘J=J∘E_(p,q) on the full qutrit input. Its output is then code-supported on every input, so the saturated-path constraint applies. The survival probabilities are p_1=p, p_2=q, p_3=1. Since p≤q and both adjacent retained coherences saturate their smaller survival probability, λ12=p and λ23=q, that constraint forces λ13=p. But E_(p,q) has λ13=0 and p>0, a contradiction.

This excludes every finite physical LOSR realization of the full channel, including competitors initially allowed to leak outside the code: exact equality to the target itself forces code support, which is the premise of §54. It does not merely exclude the pairwise constructions displayed above. The contradiction occurs at the action on a single coherent matrix unit, so matching all three basis populations is insufficient.

There is also a strictly positive, though not quantified here, unrestricted diamond separation. In fixed dimension the set of local CPTP maps is compact; its set of product channels is compact; and its convex hull is compact in the finite-dimensional real space of Hermiticity-preserving linear maps. This convex hull is exactly the finite LOSR class by the finite-dimensional convex-hull theorem. Restriction through J is continuous. Therefore the encoded physical channel set is compact. The continuous diamond distance to J∘E_(p,q) attains its minimum; the minimum cannot be zero because exact equality has just been excluded. This establishes positivity only, not an exact numerical value or an explicit uniform lower bound across the family. As p approaches zero the obstruction may vanish.

### 61.5. Relation to existing theory and known ingredients

The argument consumes §54's arbitrary-dimensional common-channel normal form. Sections58–60 settle particular two-dimensional channel problems; the present family proves that exact feasibility of all coordinate two-dimensional restrictions does not certify a common higher-dimensional physical channel. The quantifier over pairs here means every coordinate-label pair, not every arbitrary two-dimensional subspace. The fixed qutrit encoding and all coherent matrix units are retained throughout, so the obstruction concerns common implementation rather than independent state conversion.

Choi positivity, Gram representations and equality in Cauchy–Schwarz, and finite-dimensional convex-hull compactness are standard ingredients. PIO constructions and their relation to zero-communication transformations of maximally correlated systems are established background: Chitambar–Gour, Phys. Rev. A94,052336 (2016), https://link.aps.org/accepted/10.1103/PhysRevA.94.052336 . Their forward PIO construction is not asserted to classify all arbitrary-dimensional local CPTP maps. A standard reference for Choi matrices and channels is Watrous, The Theory of Quantum Information (2018), https://cs.uwaterloo.ca/~watrous/TQI/ . No literature-priority claim is made for these ingredients. The result established here is the explicit CPTP family with pairwise coherent implementations and the proved obstruction to one full-code physical LOSR implementation; it is not a general gravitational or RT recovery theorem.

## 62. A quantitative qutrit common-channel obstruction allowing physical leakage

### 62.1. Model and explicit bounds

Use the fixed MC encoding J(T)=VTV* with V|i>=|ii>, and the qutrit channel E_(p,q) of §61, where 0<q<1 and 0<p≤q(1−q). Competitors are all finite physical LOSR channels Φ=Σ_b w_b A_b⊗B_b on the two physical qutrits. They need not preserve the code. The error is the unhalved diamond norm

    δ(Φ)=||Φ∘J−J∘E_(p,q)||_diamond,

including arbitrary passive references. Then

    [2p/(10+sqrt(100+38p))]^2 ≤ inf_Φ δ(Φ) ≤ p/2.

At the explicit CPTP point p=1/4,q=1/2, this gives

    [1/(2(10+sqrt(219/2)))]^2 ≤ inf_Φ δ(Φ) ≤ 1/8.

The lower bound is strictly positive and explicit; the two bounds are not claimed equal or sharp. The upper bound is realized by one finite common physical channel on the whole qutrit input, not separate optimizers for different pairs.

### 62.2. A dimension-independent inequality for actual physical outputs

The following estimate holds in every dimension d≥3, with any three distinct labels renamed 1,2,3. For a physical LOSR channel Φ, let

    p_i = <ii|Φ(J(|i><i|))|ii>,
    λ_ij = <ii|Φ(J(|i><j|))|jj>,
    ℓ_i = Tr[(I−P_code) Φ(J(|i><i|))],

where P_code=Σ_k |kk><kk|. Thus ℓ_i is the actual basis-input code leakage. Define the real functional

    W(Φ)=2 Re λ12+2 Re λ23−Re λ13−p_1−2p_2.

Then

    W(Φ) ≤ 3 sqrt(2ℓ_1)+4 sqrt(2ℓ_2)+3 sqrt(2ℓ_3)+2ℓ_1+4ℓ_2.       (1)

In particular, exact code support implies W≤0. This linear three-label constraint strengthens the saturated-path contradiction into a usable stability estimate. Its constants do not depend on d, branch count, or local Stinespring environment dimensions.

Proof. First consider one positive-weight product branch A⊗B. Choose finite Stinespring isometries and expand their images of the input basis as

    U_A|i>=Σ_k |k> a_(k,i),    U_B|i>=Σ_k |k> b_(k,i),

where the a and b are environment vectors. Put a^i_k=||a_(k,i)||² and b^i_k=||b_(k,i)||²; each is a probability distribution. The branch's leakage on input i is

    ℓ_(b,i)=1−Σ_k a^i_k b^i_k.

Choose f_b(i) maximizing a^i_k b^i_k, and write M_(b,i) for that maximum. Cauchy–Schwarz gives Σ_k sqrt(a^i_k b^i_k)≤1, hence

    1−ℓ_(b,i)=Σ_k a^i_k b^i_k ≤ sqrt(M_(b,i)),
    1−M_(b,i) ≤ 2ℓ_(b,i).

For each i let e_(b,i) be the unit environment vector obtained by normalizing a_(f_b(i),i)⊗b_(f_b(i),i). If this vector is zero, choose any unit vector in the same environment space; in that case M_(b,i)=0 and ℓ_(b,i)=1. Define

    g_(b,i)=a_(i,i)⊗b_(i,i),
    h_(b,i)=1_(f_b(i)=i) e_(b,i).

If f_b(i)=i, then g_(b,i)=sqrt(M_(b,i)) e_(b,i). Otherwise ||g_(b,i)||²≤1−M_(b,i), since its output probability is disjoint from the maximizing joint output. In both cases,

    ||g_(b,i)−h_(b,i)||²≤2ℓ_(b,i),
    | ||g_(b,i)||²−||h_(b,i)||² |≤2ℓ_(b,i).                 (2)

The vectors g encode the actual retained matrix-unit coefficients:

    p_i=E_b ||g_(b,i)||²,    λ_ij=E_b <g_(b,j),g_(b,i)>.

Define rounded quantities p̃_i=E_b ||h_(b,i)||² and λ̃_ij=E_b <h_(b,j),h_(b,i)>. All g and h have norm at most one. The triangle inequality followed by Cauchy–Schwarz in the branch probability space yields

    |p_i−p̃_i|≤2ℓ_i,
    |λ_ij−λ̃_ij|≤sqrt(2ℓ_i)+sqrt(2ℓ_j).                    (3)

No physical implementation of the rounded vectors is asserted or needed. They are auxiliary vectors on a single common branch probability space.

For each branch write E_i=1_(f_b(i)=i), so h_i=E_i e_i. The following pointwise Gram/event inequality holds:

    2 Re<h_2,h_1>+2 Re<h_3,h_2>−Re<h_3,h_1>
       ≤ ||h_1||²+2||h_2||².                              (4)

To verify it, if all three E_i equal one, subtracting the left side from the right side gives ||e_1−2e_2+e_3||²/2≥0. If E_1=E_2=1,E_3=0, the left side is at most2 while the right side is3. If E_1=E_3=1,E_2=0, the left side is at most1 and the right side is1. If E_2=E_3=1,E_1=0, the left side is at most2 and the right side is2. With at most one event present, the left side vanishes and the right side is nonnegative. These cases exhaust all possibilities.

Averaging (4) gives W̃≤0. Applying (3) to its three coherence coefficients with absolute weights2,2,1, and its population coefficients with weights1,2, proves (1). In particular the square-root coefficients are3,4,3. This proof uses the actual arbitrary local channels, not a code-preserving ansatz or an assumed approximate version of §54.

### 62.3. From the output inequality to an unrestricted diamond certificate

Let Ψ=Φ∘J and Ψ_*=J∘E_(p,q), and set δ=||Ψ−Ψ_*||_diamond. Each basis input is a normalized density operator. Its output difference is Hermitian and trace zero, with trace norm at most δ. For any effect 0≤F≤I, its expectation difference is therefore at most δ/2 in absolute value. Since the target output has no leakage,

    ℓ_i≤δ/2,    |p_i−p_i^*|≤δ/2.

For off-diagonal input |i><j|, the input trace norm is one. By the definition of the diamond norm, ||(Ψ−Ψ_*)(|i><j|)||_1≤δ; taking the indicated matrix element gives

    |λ_ij−λ_ij^*|≤δ.

There is no use here of an unnormalized Choi entry as a diamond witness. These are direct norm consequences on normalized states or trace-norm-one matrix units. They remain valid when the definition optimizes over arbitrary references.

For the target, p_1^*=p,p_2^*=q, λ12^*=p,λ23^*=q,λ13^*=0, so W(Ψ_*)=p. The total coefficient error in W is at most (2+2+1)δ+(1+2)δ/2=13δ/2. Combining this with (1) gives

    p ≤ W(Φ)+13δ/2 ≤ 10sqrt(δ)+(19/2)δ.

Writing x=sqrt(δ) and solving the increasing quadratic on x≥0 gives

    x ≥ (sqrt(100+38p)−10)/19
      = 2p/(10+sqrt(100+38p)),

which proves the lower bound. The basis-state trace-zero argument explains all factors of two.

### 62.4. A finite common-channel upper bound

Let P=|1><1| and Q=|2><2|+|3><3| on a physical qutrit. Let S=P−Q, and let D=(3/4)id+(1/4)Ad_S. Thus D retains all populations and the23 coherence, while multiplying both12 and13 coherences by1/2. Define the local CPTP map

    F(T)=QTQ+|3><1|T|1><3|,

whose Kraus matrices are Q and |3><1|. Let R3 be the product channel resetting both physical outputs to |3>. The common physical LOSR channel

    Φ_up=p(D⊗id)+(q−p)(F⊗F)+(1−q)R3

has nonnegative weights summing to one. It has exactly the target's populations, retained coherence coefficients λ12=p/2, λ23=q, λ13=p/2, and no other code coherences. Hence its only differences from the target are the two coefficients +p/2 on12 and −p/2 on13, together with their adjoints.

To evaluate its full diamond error, work on the logical qutrit and define O(T)=PTQ+QTP=(T−STS)/2, and U=diag(1,1,−1). The logical difference is

    Δ=(p/2) Ad_U∘O.

The triangle inequality and the diamond norm one of unitary channels give ||O||_diamond≤1. Equality follows from the normalized input (|1>+|2>)/sqrt(2), whose O-image has eigenvalues1/2,−1/2 and0. Unitary conjugation and the isometric output encoding preserve the diamond norm. Therefore the displayed common implementation has error exactly p/2, including arbitrary references. This establishes the upper bound without identifying it as optimal.

### 62.5. Scope and sources

Section61 supplied exact incompatibility and a compactness-only positive gap. The present estimate supplies an explicit leakage-tolerant gap and a finite coherent full-code upper construction. The general inequality (1) applies in every finite dimension to any three selected labels. The result does not determine the exact global projection of the qutrit family, nor give a uniform positive gap as p tends to zero.

Stinespring dilation, Cauchy–Schwarz, the trace-zero effect bound and elementary diamond-norm properties are standard; see Watrous, The Theory of Quantum Information (2018), https://cs.uwaterloo.ca/~watrous/TQI/ . The finite dephasing/label constructions use the established local incoherent-operation background already attributed in §§54 and61; see Chitambar–Gour, Phys. Rev. A94,052336 (2016), https://link.aps.org/accepted/10.1103/PhysRevA.94.052336 . No literature-priority, formal-kernel, arbitrary-channel, or full RT recovery claim is made.

## 63. Exact common implementation of coherent star compression

### 63.1. Channel family and physical model

Let m≥1 and let the logical input have orthonormal labels 1,...,m,h. The output is a qubit with labels0,1. Fix the MC encodings V_in|i>=|ii> and V_out|a>=|aa>. For z∈C^m define E_z on input matrix units by

    E_z(ii)=00 (1≤i≤m),    E_z(hh)=11,
    E_z(ij)=0 (i≠j≤m),
    E_z(ih)=z_i 01,    E_z(hi)=conj(z_i)10.

Physical competitors are finite LOSR mixtures of arbitrary local CPTP maps from C^(m+1) to C². The same physical channel must act on every coherent input and every reference extension.

Then:

1. E_z is CPTP exactly when ||z||₂≤1.
2. There exists a physical LOSR channel Φ with Φ∘J_in=J_out∘E_z exactly when ||z||₁≤1. Whenever feasible, a single product of two local CPTP maps suffices; shared randomness adds no implementability in this family.
3. Every coordinate two-label restriction of every CPTP E_z has an exact physical product-channel implementation. Thus for m≥2 any z with ||z||₂≤1<||z||₁ gives a pairwise/global coherent separation. The symmetric example z_i=1/sqrt(m) has this property.
4. Among all physical LOSR competitors constrained to reproduce the displayed basis outputs exactly, the optimal unhalved diamond error is the Euclidean distance from z to the complex unit ℓ₁ ball. A single product channel attains it, with the explicit threshold formula below.

The basis-output constraint in item4 is essential to its claimed scope. No equality with the unrestricted leakage-allowing diamond optimum is asserted. Item2, being exact implementation, has no extra constraint: equality itself enforces those basis outputs.

### 63.2. Complete positivity and a direct dilation

The only nonzero block of the input-first Choi matrix, indexed by |i,0> for leaves and |h,1>, is

    [[I_m,z],[z*,1]].

Its positivity is equivalent to 1−Σ_i|z_i|²≥0 by the Schur complement of I_m. Trace preservation follows directly from the specified matrix units.

Equivalently, choose an environment with orthonormal e_0,e_1,...,e_m and set

    a=Σ_i conj(z_i)e_i+sqrt(1−||z||₂²)e_0.

The map |i>→|0>e_i, |h>→|1>a is an isometry. Its channel has exactly the stated action, since <a,e_i>=z_i with the inner product conjugate-linear in its first argument. This is a logical-channel dilation; it does not yet give a physical local implementation on the MC code.

### 63.3. Necessity from the actual common local channels

Suppose a finite physical LOSR channel realizes E_z. On every basis input |ii>, its output is the pure product |00>, and on |hh> its output is |11>. A convex combination of density matrices equals a pure state only if every positive-weight summand is that same pure state. Consequently every positive-weight product branch has local output |0> on each leaf and |1> on the hub, on both parties.

Take a Stinespring isometry for each local map in a branch. Purity of these local basis outputs forces the forms

    U_A|i>=|0>a_i,    U_A|h>=|1>a_h,
    U_B|i>=|0>b_i,    U_B|h>=|1>b_h,

with all environment vectors unit. Isometry of U_A implies that a_1,...,a_m are orthonormal, and similarly b_1,...,b_m. Put α_i=<a_h,a_i>, β_i=<b_h,b_i>. The branch's retained leaf–hub coefficient is α_iβ_i. Bessel's inequality gives Σ|α_i|²≤1 and Σ|β_i|²≤1, so

    Σ_i |α_iβ_i|≤1.

For the common mixture, z_i=Σ_b w_b α_(b,i)β_(b,i). The triangle inequality and the preceding branch estimate give ||z||₁≤1. This uses unrestricted local CPTP maps and their actual dilations, not an incoherent-operation ansatz. It also shows that any physical competitor with the same exact basis outputs necessarily equals J_out∘E_w on the full encoded input for some ||w||₁≤1: same-fiber orthogonality kills every distinct leaf–leaf matrix unit, and all remaining units have the displayed form.

### 63.4. Sufficiency by one product channel

Let s=Σ_i|z_i|≤1. Choose phases θ_i with z_i=|z_i|exp(iθ_i), taking θ_i=0 when z_i=0. With orthonormal environment vectors e_0,e_1,...,e_m, set

    a_i=b_i=e_i,
    a_h=Σ_i sqrt(|z_i|)exp(−iθ_i)e_i+sqrt(1−s)e_0,
    b_h=Σ_i sqrt(|z_i|)e_i+sqrt(1−s)e_0.

These are unit vectors, and the two maps |i>→|0>a_i, |h>→|1>a_h and their B versions are isometries. Their product channel acts on an encoded leaf–hub unit with coefficient

    <a_h,a_i><b_h,b_i>=z_i.

It acts correctly on every other encoded matrix unit. Therefore equality holds as linear maps and after tensoring with every passive reference. The construction uses environments of dimension m+1, finite local Kraus families, and no shared random branch selection.

For a coordinate pair {i,h}, the same construction needs only the one coefficient z_i, whose modulus is at most1 for every CPTP member. Extend the local maps arbitrarily and trace-preservingly on the other basis labels, for example by measuring the orthogonal complement and preparing |0>. For a pair of leaves, both local channels can reset to |0>. These are exact maps on the complete two-label algebra, including coherences; their full logical output is the qubit.

### 63.5. Exact constrained diamond projection and threshold attainer

For any z,w let v=z−w. The difference E_z−E_w has only leaf–hub matrix units, with coefficients v_i. Its diamond norm is

    ||E_z−E_w||_diamond=||v||₂.                            (1)

If v=0 this is immediate. Otherwise let r=||v||₂ and let |a>=Σ_i conj(v_i)|i>/r in the leaf space. Define a CPTP compression C from the logical input to a qubit using the Kraus operator K=|0><a|+|1><h| and additional Kraus operators |0><b_j| for an orthonormal basis of the leaf-space complement of a. Let O(T)=(T−ZTZ)/2 be the qubit off-diagonal map. Directly on every matrix unit,

    E_z−E_w=r O∘C.

The diamond norm of O is1, because it is half the difference of two unitary channels and achieves trace norm1 on |+><+|. Thus the diamond norm is at most r even with arbitrary references. On the normalized input (|a>+|h>)/sqrt(2), the output difference has eigenvalues r/2 and−r/2, giving the matching lower bound. Isometric MC output encoding preserves this norm.

The characterization above therefore reduces the basis-preserving physical optimum exactly to min_{||w||₁≤1}||z−w||₂. If ||z||₁≤1 choose w=z. Otherwise there is a unique τ>0 satisfying

    Σ_i max(|z_i|−τ,0)=1,

and an optimizer is

    w_i=exp(i arg z_i) max(|z_i|−τ,0),
    optimal error=sqrt(Σ_i min(|z_i|,τ)²).                 (2)

Here zero coordinates have arbitrary phase. For completeness, phase alignment cannot increase squared Euclidean distance, so it suffices to project the nonnegative vector a_i=|z_i| onto x_i≥0,Σx_i≤1. Set y_i=max(a_i−τ,0). On active coordinates a_i−y_i=τ, and on inactive coordinates a_i≤τ. For any feasible x,

    Σ_i(a_i−y_i)(x_i−y_i)≤τ(Σ_i x_i−Σ_i y_i)≤0.

Expanding ||a−x||₂² around y proves optimality. Strict convexity gives uniqueness. Existence and uniqueness of τ follow continuity and strict decrease of Σ_i max(a_i−τ,0) until it reaches zero. The single-product construction above implements the resulting w, so the exact optimum is attained by an actual common channel, not just a scalar relaxation.

For z_i=1/sqrt(m), the constrained optimum has w_i=1/m and error1−1/sqrt(m). This quantitative statement remains within the exact-basis-output class; unrestricted physical leakage may improve it.

### 63.6. Relation to prior results and boundaries

Section54 supplies the general physical normal-form perspective, while §§61–62 exhibit a qutrit obstruction and unrestricted leakage bounds. This family gives a complete all-dimensional common-implementation criterion and an exact coherent diamond projection under a stated basis-output constraint. Pure-output forcing, Bessel/Cauchy–Schwarz, Choi positivity, and Euclidean ℓ₁-ball projection are standard ingredients. The physical conclusion concerns the same pair of local channels on the entire input algebra, not independent state conversions.

For standard channel, dilation and diamond facts see Watrous, The Theory of Quantum Information (2018), https://cs.uwaterloo.ca/~watrous/TQI/ . PIO and zero-communication MC constructions are established background, as discussed by Chitambar–Gour, Phys. Rev. A94,052336 (2016), https://link.aps.org/accepted/10.1103/PhysRevA.94.052336 . These citations are not claimed to state the exact family characterization above, and no literature-priority claim is made. This is paper mathematics, not a compiled formal theorem or a full RT recovery result.

## 64. Unrestricted physical diamond projection for coherent star compression

### 64.1. Statement and scope

Use §63's m-leaf star-compression channel E_z, with m≥1, logical input C^(m+1) labelled1,...,m,h, logical output C², and ||z||₂≤1. Its basis action sends every leaf to0 and the hub to1; E_z(ih)=z_i01, with distinct leaf–leaf coherences killed. The input and output MC encodings are J_in and J_out.

For all finite physical LOSR channels Φ from the two local (m+1)-dimensional inputs to the two local qubit outputs, without restrictions on their populations, code support, or other matrix-unit coefficients,

    inf_Φ ||Φ∘J_in−J_out∘E_z||_diamond
       = min_{||w||₁≤1} ||z−w||₂.                         (1)

The norm is the unhalved diamond norm, including arbitrary passive references. The optimum is attained by one product of local CPTP maps. Thus the exact-basis-output restriction in §63's projection calculation can be removed for this entire family: a calibrated optimizer exists even among unrestricted physical competitors. This is not an assertion that arbitrary physical competitors are calibrated.

Explicitly, if ||z||₁≤1 the optimum is zero. Otherwise let τ>0 solve Σ_i max(|z_i|−τ,0)=1. Then

    w_i=exp(i arg z_i)max(|z_i|−τ,0),
    optimum=sqrt(Σ_i min(|z_i|,τ)²).                      (2)

For z_i=1/sqrt(m), the unrestricted optimum is exactly1−1/sqrt(m), attained by w_i=1/m. This includes m=1, when the value is zero. Every coordinate pair nevertheless has an exact physical implementation, as in §63.

### 64.2. A retained-coherence constraint for every physical competitor

For an arbitrary Φ define the retained coefficients

    λ_i=<00|Φ(|ii><hh|)|11>,    1≤i≤m.

Then, without assuming anything about Φ's basis outputs or leakage,

    ||λ||₁≤1.                                             (3)

Proof. In one product branch A⊗B choose Stinespring isometries and write

    U_A|i>=|0>a_(0,i)+|1>a_(1,i),
    U_B|i>=|0>b_(0,i)+|1>b_(1,i),

for every leaf and hub label. Define C_A:C^m→H_EA by C_A e_i=a_(0,i). It is a contraction: it is the composition of the isometric inclusion of the leaf subspace, U_A, and the output-0 coordinate projection. Thus ||C_A||≤1. Also ||a_(1,h)||≤1. For

    α_i=<a_(1,h),a_(0,i)>,

the vector α is the coordinatewise conjugate of C_A* a_(1,h), with the inner product conjugate-linear in its first variable. Hence Σ_i|α_i|²≤1. The same construction gives β_i=<b_(1,h),b_(0,i)> with Σ_i|β_i|²≤1.

The actual channel formula gives λ_i^(b)=α_iβ_i. Consequently

    Σ_i|λ_i^(b)|≤sqrt(Σ_i|α_i|²)sqrt(Σ_i|β_i|²)≤1.

A finite LOSR mixture has λ_i=Σ_b w_b λ_i^(b). The triangle inequality proves (3). In particular the environment vectors a_(0,i) have not been assumed orthogonal or normalized; contraction of their column map replaces the calibrated orthonormal-record premise. Arbitrary product ancillas and larger local environments are absorbed into the Stinespring representations. No code projection, postselection, or physical retraction is used.

### 64.3. A normalized two-dimensional-reference witness

Let Δ=J_out∘E_z−Φ∘J_in and d=z−λ. We claim

    ||Δ||_diamond≥||d||₂.                                 (4)

If d=0 the claim is immediate. Otherwise set r=||d||₂ and

    |a>=Σ_i conj(d_i)|i>/r.

This is a normalized vector in the leaf subspace. First, the trace-norm-one matrix unit |a><h| satisfies

    <00|Δ(|a><h|)|11>=Σ_i conj(d_i)d_i/r=r.

The trace norm dominates any matrix element, so the definition of the diamond norm already implies (4).

The same constant can be witnessed using a positive input state and a two-dimensional passive reference. Take

    |Ψ>=(|0>_R|a>+|1>_R|h>)/sqrt(2),
    H=|0,00><1,11|+|1,11><0,00|.

The input is normalized and H is Hermitian with operator norm1. In (id_R⊗Δ)(|Ψ><Ψ|), the indicated off-diagonal entry is r/2 and its adjoint is r/2. Its other entries do not contribute to the expectation of H. Therefore

    Tr[H (id_R⊗Δ)(|Ψ><Ψ|)]=r,

and trace-norm duality proves (4) with no omitted factor of two. This explicitly handles arbitrary competitor populations, extra coherences and leakage: the reference blocks and the two selected output entries isolate the coefficient difference.

Combining (3) and (4), every physical competitor obeys

    ||Δ||_diamond≥||z−λ||₂≥min_{||w||₁≤1}||z−w||₂.

The witness depends on the competitor through d, which is permitted in the supremum defining its diamond error. It is a bound for one common channel on all inputs, not separate sector optimizations.

### 64.4. Matching finite common-channel attainment

Section63 constructs, for every ||w||₁≤1, a single product of two local CPTP maps Φ_w satisfying Φ_w∘J_in=J_out∘E_w on all encoded matrix units and all reference extensions. It also proves

    ||J_out∘E_z−J_out∘E_w||_diamond=||z−w||₂,

by an explicit CPTP compression followed by the off-diagonal qubit map. Choose the Euclidean projection w onto the unit ℓ₁ ball. The finite-dimensional ball is compact, so this choice attains the minimum; §63's threshold proof gives exactly (2). The corresponding product channel supplies the upper bound equal to the lower bound above. Both local environments may be taken of dimension m+1.

For the symmetric vector, permutation symmetry or the threshold formula gives w_i=1/m and ||z−w||₂=1−1/sqrt(m). Thus the common-channel error approaches1 in this normalization as the number of individually compatible leaf–hub pairs grows. This is a dimension-dependent exact result, rather than a compactness-only separation.

### 64.5. Relation to existing theory

Section63 established exact implementability and the calibrated projection. The new step is (3) for actual unrestricted local CPTP outputs, followed by the normalized reference witness. Neither pure basis outputs nor exact code support is assumed in this step. Section62's leakage estimate is not needed for this family.

Stinespring dilation, adjoint contraction, Cauchy–Schwarz, trace-norm duality and the diamond norm are standard; see Watrous, The Theory of Quantum Information (2018), https://cs.uwaterloo.ca/~watrous/TQI/ . The known local incoherent-operation background and the finite constructions used in §63 retain their attribution to Chitambar–Gour, Phys. Rev. A94,052336 (2016), https://link.aps.org/accepted/10.1103/PhysRevA.94.052336 . No priority claim is made for these ingredients. The result concerns the stated all-dimensional coherent star family and fixed MC encodings, not all logical channels or full RT recovery; it is a paper proof without a formal-kernel claim.

## 65. Exact unrestricted common-channel projection for two collapsed fibres

### 65.1 Physical family and result

Let m,n≥1. The logical input has disjoint orthonormal labels a_1,...,a_m and b_1,...,b_n; the logical output is a qubit. Fix input and output MC encodings J_in(T)=V_in T V_in*, V_in|x>=|xx>, and V_out|s>=|ss>. For Z∈C^(m×n), define E_Z by

    E_Z(a_i a_k)=δ_ik 00,    E_Z(b_j b_l)=δ_jl 11,
    E_Z(a_i b_j)=Z_ij 01,    E_Z(b_j a_i)=conj(Z_ij)10.

Matrix units are denoted by their two labels. Define the compact convex set

    S_(m,n)={W: Σ_j|W_ij|≤1 for every i,
                  Σ_i|W_ij|≤1 for every j}.

Then:

1. E_Z is CPTP iff ||Z||op≤1.
2. E_Z has an exact physical LOSR implementation on the whole MC code iff Z∈S_(m,n).
3. For every CPTP E_Z, allowing arbitrary physical output populations, extra coherences and leakage,

    inf_Φ ||Φ∘J_in−J_out∘E_Z||diamond
       = min_(W∈S_(m,n)) ||Z−W||op.                      (1)

Here Φ ranges over finite mixtures of product local CPTP maps C^(m+n)→C². The same physical channel acts on all inputs and reference extensions, and the diamond norm is unhalved. The minimum is attained by a finite common LOSR channel with at most mn+1 product branches. A single product branch need not suffice; an explicit example below has minimum branch count two.

For n=1, S_(m,1) is the complex unit ℓ₁ ball and the operator norm is the vector ℓ₂ norm, recovering §64. For general m,n, (1) is an exact finite convex optimization, not a claimed elementary closed formula.

### 65.2 Complete positivity and the unrestricted retained matrix

The only nonzero Choi block of E_Z, on |a_i,0> and |b_j,1>, is

    [[I_m,Z],[Z*,I_n]].

It is positive semidefinite iff ||Z||op≤1, by the Schur complement. Trace preservation is immediate from the matrix units.

For an arbitrary physical competitor define

    Λ_ij=<00|Φ(|a_i a_i><b_j b_j|)|11>.

We claim Λ∈S_(m,n) without any calibration or support assumption. In one local Stinespring representation write U_A|x>=|0>u_(0,x)+|1>u_(1,x), and similarly U_B with vectors v. Let C_A:C^m→H_EA map e_i to u_(0,a_i), and D_A:C^n→H_EA map e_j to u_(1,b_j). Both are contractions, being coordinate projections of an isometry restricted to a subspace. The matrix

    R_ij=<u_(1,b_j),u_(0,a_i)>

is the entrywise conjugate of C_A*D_A, so ||R||op≤1. Likewise the matrix T for the B party is a contraction. The actual product branch has retained matrix R⊙T.

Each row and each column of a contraction has Euclidean norm at most one. Cauchy–Schwarz therefore gives

    Σ_j|R_ij T_ij|≤1,    Σ_i|R_ij T_ij|≤1.

Finite convex mixtures preserve both bounds by the triangle inequality. Thus Λ∈S_(m,n). The proof does not assume that the output-coordinate environment vectors within a fibre are orthogonal or normalized; it uses their column-map contractions. It covers arbitrary local ancillas through Stinespring dilation.

This already proves exact-implementation necessity. It also implies that every W∈S is a contraction: the standard bound ||W||op²≤||W||_(1→1)||W||_(∞→∞) gives ||W||op≤1. Alternatively this follows from the convex decomposition constructed next.

### 65.3 Signed partial matchings give finite physical sufficiency

Let W∈S and put P_ij=|W_ij|. This is a rectangular doubly substochastic matrix. To see its finite partial-permutation decomposition directly from Birkhoff's theorem, let r_i=1−Σ_jP_ij and c_j=1−Σ_iP_ij. The square matrix

    [[P,diag(r)],[diag(c),P^T]]

of size m+n is nonnegative with every row and column sum one. Decompose it into a convex combination of permutation matrices. Their upper-left blocks are m×n partial permutation matrices, proving P=Σ_t w_t P_t. By Carathéodory in R^(mn), at most mn+1 such blocks are needed, including a zero block if necessary.

Choose phases θ_ij with W_ij=P_ij exp(iθ_ij), arbitrarily when P_ij=0. Give every selected entry of P_t this phase to obtain a signed partial matching Q_t. Then W=Σ_t w_t Q_t.

Each Q_t has an exact product-channel implementation. For each matching choose orthonormal environment records for all A-fibre labels and all B-fibre labels, identifying the record for a_i with the record for b_j precisely when (i,j) is matched. All unmatched records and records of distinct matching pairs are mutually orthogonal. Within each fibre the records are therefore orthonormal. On the first party multiply the b_j record of a matched pair by exp(−iθ_ij); on the second party use the unphased records. Define local isometries by

    |a_i>→|0>e_i,    |b_j>→|1>f_j,

using those phased or unphased records on the respective party. Cross-fibre input orthogonality is enforced by the output0/1 labels. The product of the two local cross-record overlaps is exactly (Q_t)_ij; same-fibre off-diagonal units vanish. Thus the product channel implements E_(Q_t) on all encoded matrix units. Both environments can be chosen of dimension at most m+n.

Mixing these product channels with weights w_t implements E_W. This supplies one common finite channel, not a separate choice for each matrix entry. Equality of the full linear maps implies equality after all passive reference extensions. It also proves finite attainment once an optimizing W is chosen.

The partial-permutation convex-hull theorem and its branch decomposition are classical Birkhoff-type facts, not new matrix-combinatorics claims.

### 65.4 Exact difference norm and unrestricted lower witness

For any two matrices Z,W, including matrices whose individual channels are not positive, their prescribed linear-map difference satisfies

    ||E_Z−E_W||diamond=||Z−W||op.                         (2)

Let D=Z−W and r=||D||op. For r=0 this is immediate. Otherwise E_(D/r) is CPTP by the Choi criterion above. If O(T)=(T−σ_z T σ_z)/2 is the qubit off-diagonal map, then

    E_Z−E_W=r O∘E_(D/r).

The diamond norm of O is one: the unitary-channel triangle inequality bounds it by one and the state |+><+| attains one. This proves the upper bound r for arbitrary references and arbitrary operator inputs.

There exist normalized vectors |a> in the first fibre and |b> in the second such that

    Σ_ij a_i conj(b_j)D_ij=r,

after adjusting a global phase. Indeed this is the usual singular-vector variational formula for ||D||op with the first vector conjugated; conjugation does not change its unit sphere. The normalized state (|a>+|b>)/sqrt(2) has difference output with off-diagonal entries r/2, so its trace norm is r. This proves (2); isometric output encoding preserves the norm.

For an unrestricted physical Φ let Λ be its retained matrix, D=Z−Λ and r=||D||op. Choose the same maximizing a,b and a two-dimensional passive reference. Put

    |Ψ>=(|0>_R|a>+|1>_R|b>)/sqrt(2),
    H=|0,00><1,11|+|1,11><0,00|.

The input is normalized and ||H||op=1. For Δ=J_out∘E_Z−Φ∘J_in,

    Tr[H(id_R⊗Δ)(|Ψ><Ψ|)]=r.

Only the two reference-off-diagonal output entries contribute, each r/2; arbitrary populations, extra coherences and leakage cannot alter this expectation. Consequently ||Δ||diamond≥||Z−Λ||op. Since Λ∈S, this proves the lower bound in (1). A minimizer W exists because S is compact. Its finite physical construction and (2) give the matching upper bound, completing the unrestricted result.

### 65.5 An explicit finite convex program

Formula (1) can be evaluated as a semidefinite program with complex matrix W, real variables t_ij≥0 and δ≥0:

    minimize δ,
    [[δ I_m,Z−W],[(Z−W)*,δ I_n]] ≥0,
    [[t_ij,W_ij],[conj(W_ij),t_ij]] ≥0 for every i,j,
    Σ_j t_ij≤1 for every i,    Σ_i t_ij≤1 for every j.

The two-by-two constraints say t_ij≥|W_ij|, so their projection is exactly S. The first constraint says ||Z−W||op≤δ, including δ=0. Complex Hermitian constraints can equivalently be written as real symmetric constraints by the usual realification. This is an exact description with a proved finite physical attainer, not a relaxation of the physical optimum. No closed-form solution or computational complexity claim is made for general Z.

### 65.6 Shared randomness can be strictly necessary

Take m=n=3 and

    W=(1/2)[[1,1,0],[1,0,1],[0,1,1]].

It lies in S and is therefore CPTP and exactly physically implementable. It is half the sum of the permutation matrices with supports {(1,1),(2,3),(3,2)} and {(1,2),(2,1),(3,3)}, so two product branches suffice.

No single product channel implements it. Exact basis outputs are pure, so a putative product realization has local orthonormal records within each fibre, with cross-record contraction matrices R,T satisfying W=R⊙T. In every row,

    1=Σ_j|R_ij T_ij|≤||R_i||₂||T_i||₂≤1.

Equality forces both row norms to be one and |R_ij|=|T_ij| for every j. Therefore |R_ij|²=W_ij. Since R is a square contraction with every row norm one, RR*≤I and Tr(RR*)=3; positivity of I−RR* forces RR*=I, so its rows are orthonormal. But its first and second rows overlap in exactly one nonzero column, with overlap modulus1/2. They cannot be orthogonal, a contradiction. Thus the minimum number of product branches for exact implementation is exactly two.

This uses the familiar obstruction to a bistochastic matrix being the squared moduli of a unitary matrix. The contribution here is its role in the actual common-channel resource count, not a new unistochastic-matrix obstruction.

### 65.7 Attribution and boundaries

The retained-matrix contraction proof extends §64's vector argument to two arbitrary fibres. The physical matching construction and unrestricted reference witness establish the exact channel reduction. Pairwise feasibility alone is insufficient whenever a contraction Z lies outside S, while shared randomness has a separate role even inside S as the example shows.

Birkhoff and doubly substochastic decompositions are established matrix theory; see Lei Cao, A short note on doubly substochastic analog of Birkhoff's theorem, https://arxiv.org/abs/1801.01232 . Unistochastic matrices and the distinction from bistochastic matrices are standard; see Bengtsson, Ericsson, Kuś, Tadej and Życzkowski, Birkhoff's polytope and unistochastic matrices, N=3 and N=4, https://arxiv.org/abs/math/0402325 . For channel and diamond facts see Watrous, The Theory of Quantum Information, https://cs.uwaterloo.ca/~watrous/TQI/ . PIO/zero-communication background remains credited to Chitambar–Gour, Phys. Rev. A94,052336 (2016), https://link.aps.org/accepted/10.1103/PhysRevA.94.052336 . These standard ingredients are not claimed novel, and no global priority claim is made for the family result.

The theorem concerns the specified two-fibre compression channels and fixed MC encodings, with unrestricted physical LOSR competitors for that target family. It does not classify arbitrary logical channels or assert full RT recovery. This is paper mathematics without a formal-kernel claim.

## 66. Exact shared-randomness cost for uniform multi-fibre compression

### 66.1 Channel family and resource statements

Let d≥2 and k≥2. The logical input has orthonormal labels |f,i>, with 1≤f≤k and 1≤i≤d; the logical output has labels |f>. Fix MC encodings J_in(|x><y|)=|xx><yy| and J_out(|f><g|)=|ff><gg|. Define the logical map F_(k,d) on all matrix units by

    F(|f,i><f,j|)=δ_ij |f><f|,
    F(|f,i><g,j|)=(1/d)|f><g|  when f≠g.

This is CPTP. Consider exact physical implementations Φ∘J_in=J_out∘F, where Φ=Σ_(t=1)^r w_t(A_t⊗B_t), all w_t>0, Σ_t w_t=1, and A_t,B_t are arbitrary local CPTP maps C^(kd)→C^k. The same channel must implement every encoded matrix unit, hence all coherent inputs and passive references. Arbitrary local ancillas and physical outputs are allowed; exactness, rather than an imposed ansatz, will force the needed output structure.

The following resource statements hold.

1. A single product channel implements F_(k,d) iff k mutually unbiased orthonormal bases exist in C^d.
2. Every exact r-branch implementation satisfies

    k(d−1)≤r(d²−1),  hence r≥ceil(k/(d+1)).                 (1)

   More strongly, every branch weight obeys w_t≤(d+1)/k. Its Shannon entropy is therefore at least max{0,log₂(k/(d+1))}.
3. An exact finite implementation exists for every k,d, with at most d^(k−1) product branches.
4. If a real Hadamard matrix of order r exists, then for d=2 and k=3r the minimum number of product branches is exactly r, and the minimum Shannon entropy of the shared branch variable is exactly log₂r. More generally the same branch minimum r holds for any 3(r−1)<k≤3r obtained by restricting this construction. For d=2, every restriction to at most three whole fibres admits one product implementation.

The last assertion concerns coordinate-fibre restrictions, not every subspace of the logical input. The entropy counts the shared classical branch variable in an exact finite LOSR decomposition; local private randomness is already absorbed into the arbitrary CPTP factors.

### 66.2 Complete positivity and branchwise pure-output records

Put u=(1,...,1)/sqrt(d). The nonzero Choi block of F has diagonal blocks I_d and off-diagonal blocks uu*. It is the sum of the positive matrices

    I_k⊗(I_d−uu*) + J_k⊗uu*,

where J_k is the all-ones matrix. Thus F is completely positive. The matrix-unit prescription is trace preserving, including distinct labels in one fibre.

For each input basis state, exactness gives

    Σ_t w_t A_t(|f,i><f,i|)⊗B_t(|f,i><f,i|)=|ff><ff|.

A convex combination of density matrices equals a rank-one projector only if every positive-weight term equals that projector: take expectations on its orthogonal complement, whose summands are nonnegative. Taking marginals therefore forces each local output to be |f><f|. In Stinespring dilations the corresponding vectors have the form

    U_A,t|f,i>=|f> e_(t,f,i),
    U_B,t|f,i>=|f> h_(t,f,i).

For each fixed t,f the d records e_(t,f,i) form an orthonormal family, as do the h records, because the dilation is isometric. No relation between different fibres has yet been assumed.

For two distinct fibres f,g define the cross-record matrices

    R_(t,fg)[i,j]=<e_(t,g,j),e_(t,f,i)>,
    T_(t,fg)[i,j]=<h_(t,g,j),h_(t,f,i)>.

They are d×d contractions, being cross-Gram matrices of two orthonormal families (up to entrywise conjugation, which preserves norm). The actual branch coefficient of |ff><gg| is R_ij T_ij. The target requires

    Σ_t w_t R_(t,fg)[i,j] T_(t,fg)[i,j]=1/d.             (2)

### 66.3 Saturation forces common spans and averaged unbiasedness

Fix f≠g and a row i. Equation (2) and Cauchy–Schwarz imply the chain

    1=Σ_j |Σ_t w_t R_t[i,j]T_t[i,j]|
      ≤Σ_t w_t Σ_j|R_t[i,j]T_t[i,j]|
      ≤Σ_t w_t ||R_t[i,:]||₂ ||T_t[i,:]||₂
      ≤Σ_t w_t=1.

All inequalities are equalities. Positivity of every w_t implies that each branch row has both norms one and equal entrywise magnitudes: |R_t[i,j]|=|T_t[i,j]|. Equality in each triangle inequality, together with the strictly positive target value 1/d, forces every nonzero product R_t[i,j]T_t[i,j] to have phase zero. Hence

    R_t[i,j]T_t[i,j]=|R_t[i,j]|²,
    Σ_t w_t |R_(t,fg)[i,j]|²=1/d.                       (3)

This includes zero entries without assigning their phase.

A square contraction R_t with every row norm one has R_t R_t*≤I and trace d, hence R_t R_t*=I. It is unitary. A unitary cross-Gram matrix between two orthonormal d-frames forces their spans to coincide: every vector of the first frame has projection norm one onto the span of the second. For each branch t, compare every fibre with fibre 1. All e frames therefore span the same d-dimensional environment space; the same is true independently of the h frames. Identify the former space with C^d. Then (3) is exactly averaged unbiasedness of k orthonormal bases in C^d, with the same weights for every pair.

Conversely, suppose such bases e_(t,f,i) and weights satisfy (3). Choose h_(t,f,i)=conjugate(e_(t,f,i)) in a fixed coordinate system. The two local isometries displayed above then have cross-coefficient |<e_(t,g,j),e_(t,f,i)>|². Their mixture implements (2). Within a fibre both records are orthonormal, so the remaining matrix units also agree. Thus these weighted basis families characterize exact finite implementation with r branches. This converse uses one globally consistent conjugate family, with no entry-dependent choice of channel.

For r=1, condition (3) is precisely the definition of k mutually unbiased bases. This proves the first resource statement in both directions.

### 66.4 Weighted Hilbert–Schmidt packing and branch entropy

Let H_0(d) be the real Hilbert space of traceless Hermitian d×d matrices, with inner product Tr(XY) and dimension d²−1. For each t,f put P_(t,f,i)=|e_(t,f,i)><e_(t,f,i)|. For real vectors x∈R^d with Σ_i x_i=0 define

    V_f x = ( sqrt(w_t) Σ_i x_i P_(t,f,i) )_(t=1)^r
             ∈ ⊕_(t=1)^r H_0(d).

Within a fibre, orthogonality of the projectors and Σ_t w_t=1 give <V_f x,V_f y>=Σ_i x_i y_i. Thus each V_f is an isometry on the (d−1)-dimensional zero-sum space. For f≠g, equation (3) gives

    <V_f x,V_g y>
       =Σ_ij x_i y_j Σ_t w_t Tr(P_(t,f,i)P_(t,g,j))
       =(1/d)(Σ_i x_i)(Σ_j y_j)=0.

The k image subspaces are mutually orthogonal. Counting dimensions proves (1).

For the stronger weight statement, combine the V_f into an isometry V from the direct sum of k zero-sum spaces into ⊕_t H_0(d). The orthogonal projection VV* is at most the identity. Its t-th diagonal block is w_t Σ_f Q_(t,f), where Q_(t,f) is the orthogonal projection onto the traceless diagonal subspace for basis (t,f). Taking the trace on that block gives

    w_t k(d−1)≤d²−1,

so w_t≤(d+1)/k. Consequently −Σ_t w_t log₂w_t≥log₂(k/(d+1)); nonnegativity of entropy supplies the stated maximum with zero. This argument allows arbitrary positive, unequal weights and arbitrarily large original local environments.

### 66.5 Finite implementations and sharp qubit constructions

Finite existence for arbitrary k,d needs no assumption about complete MUB sets. Take one fixed standard basis in C^d and assign each fibre f a cyclic shift s_f∈Z/d of that basis, with s_1=0. Average uniformly over the d^(k−1) choices of the remaining shifts. For distinct fibres the difference s_f−s_g is uniform, so every squared overlap averages to 1/d. The converse above produces an exact finite physical channel.

For the sharp qubit family let H be an r×r real Hadamard matrix, H*H=rI, with entries ±1. Label the k=3r fibres by (a,c), where a∈{X,Y,Z} is a Pauli axis and 1≤c≤r a column of H. At branch t, weight 1/r, let the two basis projectors in fibre (a,c) be

    P_(t,(a,c),i)=[I+(-1)^i H_(t,c) σ_a]/2,  i∈{0,1}.

Choose arbitrary normalized representatives e for these rank-one projectors, and use their coordinatewise conjugates on the other party. For a≠b, the squared overlap of any representatives is Tr(P_a P_b)=1/2. For a=b and c≠c',

    Tr(P_(t,(a,c),i)P_(t,(a,c'),j))
       =[1+(-1)^(i+j)H_(t,c)H_(t,c')]/2.

Hadamard column orthogonality makes its branch average 1/2. Thus all distinct fibres satisfy (3), simultaneously, and this one r-branch channel implements all coherent matrix units. The lower bound k≤3r' for any implementation with r' branches forces r'≥r. The weight bound is w_t≤1/r for any implementation; its entropy is at least log₂r, attained by the uniform construction.

Restricting to any k fibres with 3(r−1)<k≤3r preserves this r-branch construction and yields ceil(k/3)=r as lower bound. For d=2, independently, any specified subset of at most three fibres admits one product realization by assigning those fibres distinct Pauli eigenbases. Such independently feasible restrictions need not share a single product realization for the full channel when k>3.

Real Hadamard matrices are not asserted to exist at every order. Orders r=2^s are available by the classical recursion H_1=[1], H_(2r)=[[H_r,H_r],[H_r,−H_r]], whose product with its transpose is 2r I. Therefore the exact resource families include k=3·2^s for every s≥0, as well as any other given Hadamard order. For r=1 the construction is the usual three Pauli bases. The cases k=1 or d=1, outside the main assumptions, admit a single product channel and require no packing argument.

### 66.6 Attribution and mathematical boundary

The orthogonal traceless-subspace description and the classical MUB bound k≤d+1 are standard; see Boykin, Sitharam, Tiep and Wocjan, Mutually Unbiased Bases and Orthogonal Decompositions of Lie Algebras, https://arxiv.org/abs/quant-ph/0506089 . Pauli/generalized-spin constructions of MUBs are established; see Pittenger and Rubin, Mutually Unbiased Bases, Generalized Spin Matrices and Separability, https://arxiv.org/abs/quant-ph/0308142 . The Hadamard recursion is classical, and its elementary verification is included above. PIO/zero-communication background remains Chitambar–Gour, Phys. Rev. A94,052336 (2016), https://link.aps.org/accepted/10.1103/PhysRevA.94.052336 . These ingredients are not claimed new.

The channel statement extends §65's saturated two-fibre contractions to a single common implementation for all fibres. Its physical equality analysis identifies the exact weighted-basis resource, gives a branch and entropy obstruction for arbitrary product CPTP factors, and supplies sharp finite families. It is an exact-implementation resource theorem, not a positive-error diamond optimum or a classification of arbitrary RT channels. Equality of the prescribed linear maps includes all reference extensions; no global-priority claim is made.
