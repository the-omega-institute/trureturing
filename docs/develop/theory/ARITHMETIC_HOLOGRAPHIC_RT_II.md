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

## 67. Balanced real frames and exact nine-fibre randomness cost

### 67.1 Exact equality criterion for qubit fibres

Use the uniform multi-fibre compression channel F_(k,2) and fixed MC input/output encodings of §66. A physical branch is an arbitrary product of local CPTP maps; branch count and Shannon entropy refer to an exact finite LOSR decomposition, with positive weights and one common channel on all coherent inputs and passive references.

For every integer r≥1, the following are equivalent:

1. F_(3r,2) has an exact implementation using r product branches.
2. There exists a real orthogonal matrix O of size 3r whose rows are grouped into r consecutive blocks of three, such that the restriction of every column to every block has squared norm 1/r.

When these conditions hold, the minimum branch count is r and the minimum shared entropy is log₂r. Every r-branch implementation has uniform weights. The balanced-block condition concerns Euclidean norms, not equal magnitudes of all individual entries; it is weaker than a real Hadamard construction.

Proof. By the physical equality analysis of §66, each positive branch supplies a family of qubit orthonormal bases in one common two-dimensional environment. Write its rank-one projectors as

    P_(t,f,i)=[I+(-1)^i n_(t,f)·σ]/2,

where n_(t,f)∈R³ is a unit Bloch vector. Averaged unbiasedness is equivalent to

    Σ_t w_t n_(t,f)·n_(t,g)=0  for f≠g.

Thus the 3r vectors with t-th block sqrt(w_t)n_(t,f) are orthonormal columns in R^(3r). They form a square orthogonal matrix O. Its t-th three-row block has total squared Frobenius norm three, while summing its 3r column-block norms gives 3r w_t. Consequently w_t=1/r, and every column-block norm is 1/sqrt(r).

Conversely, from such O define n_(t,f)=sqrt(r) times its t-th column block, and choose the corresponding qubit eigenbases. Orthogonality of distinct columns gives average Bloch inner product zero with weights 1/r. Using conjugate records on the second party, the common physical construction in §66 implements every encoded matrix unit exactly. Its branch lower bound and weight/entropy lower bound give the stated minima. This is an equality criterion for the physical resource problem, with arbitrary original local environments already covered by §66.

### 67.2 An explicit order-three balanced block construction

Let I and J be the 3×3 identity and all-ones matrices and define

    S=[[0,-1,1],[1,0,-1],[-1,1,0]],
    C=−(I+J+sqrt(5)S)/4,
    A=(C+2I)/3,    B=(C−I)/3.

Equivalently, C is the real circulant matrix with first row (−1/2,(−1+sqrt(5))/4,(−1−sqrt(5))/4). Its subsequent rows are cyclic right shifts. The square root occurs in these exact orthogonality identities; no broader physical interpretation is needed.

Then the real 9×9 block matrix

    O=[[A,B,B],[B,A,B],[B,B,A]]                           (1)

is orthogonal, and every column in every three-row block has squared norm 1/3.

Proof. We have S^T=−S, S²=J−3I, JS=SJ=0 and J²=3J. Hence

    (I+J+sqrt(5)S)(I+J−sqrt(5)S)
       =(I+J)²−5S²=16I.

Therefore C is orthogonal, and each diagonal entry is −1/2. Let P=J/3 be the orthogonal projection onto the uniform direction in the outer block index. Since A−B=I and A+2B=C, equation (1) is

    O=P⊗C+(I−P)⊗I.

The two summands act on orthogonal outer subspaces; thus O O^T=I. For every standard coordinate vector e_j,

    ||A e_j||²=(1+4+4 C_jj)/9=1/3,
    ||B e_j||²=(1+1−2 C_jj)/9=1/3.

These are exactly all column-block norms of (1). The preceding criterion gives an exact implementation of F_(9,2) with three product branches and shared entropy log₂3; neither quantity can be smaller. All local environments in this construction have dimension two. The local isometries map |f,i> to |f> times the eigenvector of the Bloch direction sqrt(3) O_(block t,column f), and the second party uses its coordinatewise conjugate. This explicitly fixes one physical map per branch for all fibres and inputs.

There is no real Hadamard matrix of order three: the inner product of two ±1 rows of length three is an odd integer, hence cannot vanish. Thus this attainer is outside the Hadamard-order hypothesis of §66, rather than an invocation of an unknown Hadamard matrix. Restrictions to seven or eight fibres still have branch minimum three by ceil(k/3), but no entropy equality is asserted for those restrictions. Every restriction to at most three whole fibres has a single product implementation as in §66.

### 67.3 Tensor extension with existing real Hadamard orders

If H is a real Hadamard matrix of order h and O is the 9×9 matrix (1), then (H/sqrt(h))⊗O is a balanced orthogonal matrix with 3h row blocks of size three. Indeed both factors are orthogonal, and every resulting column-block squared norm is (1/h)(1/3)=1/(3h). The criterion therefore gives

    minimum branches for F_(9h,2) = 3h,
    minimum shared entropy = log₂(3h).

In particular h=2^s follows from the classical Sylvester recursion, giving an infinite exact family with 3·2^s branches. This tensor statement assumes a given Hadamard H and does not assert Hadamard existence at arbitrary orders. Nor does the nine-dimensional construction prove that balanced orthogonal frames exist for every integer r.

### 67.4 Attribution and scope

The Bloch-sphere parametrization, orthogonal projectors, and tensor products of orthogonal matrices are standard. The MUB/traceless-subspace background is credited in §66 to Boykin, Sitharam, Tiep and Wocjan, https://arxiv.org/abs/quant-ph/0506089 , and the Pauli construction to Pittenger and Rubin, https://arxiv.org/abs/quant-ph/0308142 . Hadamard recursion and its tensor closure are classical. The balanced-frame reduction here uses the actual physical saturation theorem of §66 to certify resource minima, and the displayed real matrix supplies an explicit attainer beyond its Hadamard-order hypothesis. No priority claim is made for the underlying block-matrix identities.

These statements concern exact finite physical implementation of the specified uniform multi-fibre channel family. They retain full coherent-input and arbitrary-reference equality. They give neither a general positive-error diamond formula nor arbitrary-channel or full-RT recovery.

## 68. Packed shared-entropy optimum for qubit multi-fibre channels

### 68.1 Universal entropy bound and equality criterion

Consider exact finite physical LOSR implementation of F_(k,2) from §66, with fixed MC encodings and one common channel on every coherent input and passive reference. Let k≥3 and write k=3q+s, q≥1, s∈{0,1,2}. Set

    p*=(3/k repeated q times, s/k if s>0),
    H*=−q(3/k)log₂(3/k)−(s/k)log₂(s/k),                 (1)

where the final term is zero when s=0. Every implementation has shared entropy at least H*. It has at least q+1_(s>0) product branches. Equality in the entropy bound holds only when the positive branch weights, up to permutation, are p*.

Moreover, the following are equivalent:

1. An exact finite physical implementation attains entropy H*.
2. There is a real orthogonal k×k matrix whose rows are grouped into q blocks of three and, when s>0, one final block of s, with every column having squared norm 3/k in each triple and s/k in the final block.

When these hold, one implementation simultaneously minimizes branch count and entropy. For s=0 this recovers the balanced-frame criterion of §67. The statement is an attainment criterion; it does not assert existence of these matrices for every k or a positive-error approximation result.

Proof of the bound. Every weight is at most a=3/k by §66. Among finite probability vectors with that cap, the entropy-minimizing vector is p*. A direct argument avoids an assumed optimum dimension: if two positive coordinates x≤y are both strictly below a, transfer min{x,a−y} from x to y. Strict concavity of −u log₂u shows that entropy strictly decreases under this nonzero transfer. One coordinate becomes zero or the other reaches a. Repeating finitely many times leaves at most one nonzero unsaturated coordinate. The total mass then forces precisely q coordinates equal to a and, if nonzero, the residual s/k. The same argument proves that equality requires p*. The branch bound follows from the same cap, or §66's dimension bound.

### 68.2 Physical saturation and a rectangular-frame equality analysis

The physical normal form of §66 supplies unit Bloch vectors n_(t,f)∈R³ for each branch and fibre. If w_t are the branch weights, the k vectors

    v_f=(sqrt(w_t)n_(t,f))_t

are orthonormal in R^(3r), where r is the number of positive branches. This conclusion holds for arbitrary original product CPTP factors and local environments: exact pure basis outputs and the saturated cross-coherence equations force the common-span basis structure first.

Suppose entropy H* is attained. The preceding equality condition gives r=q+1_(s>0), with q weights 3/k and an optional last weight s/k. Let V be the matrix whose columns are v_f and P=VV*, an orthogonal projection. For a branch t of weight 3/k, the corresponding 3×3 diagonal block P_tt has trace

    Σ_(f=1)^k w_t ||n_(t,f)||²=3.

Since 0≤P_tt≤I_3, it equals I_3. Positivity of I−P then forces all off-diagonal blocks incident to this block to vanish: a positive matrix with a zero diagonal compression has zero cross compression, by Cauchy–Schwarz for its positive quadratic form. Therefore, if s>0,

    P=I_(3q) ⊕ P_tail,

where P_tail is an orthogonal projection of rank s in R³; if s=0, P=I_k. An orthogonal rotation of the last three Bloch coordinates diagonalizes P_tail to I_s⊕0. This rotation preserves every column-block norm. Discarding the resulting zero rows gives a square orthogonal k×k matrix with exactly the asserted block norms. The rotation is a change in the real frame used for the existence proof; no unsupported claim that every such rotation is a local unitary is needed.

Conversely, from a matrix as in condition2, divide each column block by the square root of its assigned weight, padding the s-row block with zeros to make three coordinates. These are unit Bloch vectors. Orthogonality of the original columns gives averaged unbiasedness with weights p*. Pick qubit eigenvectors for each direction and coordinatewise conjugate records on the second party. The construction in §66 defines one product channel per branch and realizes every encoded matrix unit. Its branch count and entropy attain both bounds. All environments can have dimension two. The choice of channel is simultaneous over all fibres, rather than optimized separately for each pair.

### 68.3 Exact infinite family from scalar Hadamard matrices

Suppose a real Hadamard matrix H of order k is given. The normalized matrix H/sqrt(k) is orthogonal and every entry has squared modulus 1/k. Grouping rows into triples and a final s-row block immediately satisfies condition2. Hence F_(k,2) has exact branch minimum ceil(k/3) and exact entropy minimum H*.

In particular, for every k=2^j with j≥2, the classical Sylvester recursion supplies H, so this is an infinite family in which k need not be divisible by three. For k=4 the optimal weights are (3/4,1/4), and for k=8 they are (3/8,3/8,1/4). These weights attain the stated exact coherent-channel targets. They improve on a uniform distribution over the minimum number of branches whenever s>0: strict entropy concavity makes H*<log₂ceil(k/3).

The construction uses a scalar Hadamard matrix of order k followed by row grouping. It neither asserts a Hadamard matrix of order ceil(k/3) nor forms a tensor product of two three-dimensional Bloch frames. When no suitable matrix is supplied, (1) remains a lower bound and the equality criterion remains conditional.

### 68.4 Attribution and boundaries

The cap w_t≤3/k and physical weighted-basis characterization are the channel results of §66. The entropy minimization under a probability cap is the standard concavity/majorization principle, proved directly here. The real-frame equality analysis extends §67 from equal three-row blocks to a possible final lower-dimensional block. Hadamard matrices and the Sylvester recursion are classical; the MUB and orthogonal-subspace background is credited in §66 to Boykin, Sitharam, Tiep and Wocjan, https://arxiv.org/abs/quant-ph/0506089 , and Pittenger and Rubin, https://arxiv.org/abs/quant-ph/0308142 . No novelty claim is made for these established ingredients.

The entropy is that of the shared classical variable in an exact finite LOSR decomposition. Local private randomness is absorbed into the arbitrary local channels. The theorem supplies an exact physical resource optimum for the stated families and a general equality criterion, with all coherent inputs and passive references retained. It is not a classification of arbitrary channels or an unrestricted positive-error diamond formula.

## 69. Exact shared entropy for five and seven qubit fibres

### 69.1 Resource statement

For the uniform multi-fibre channel F_(k,2), fixed MC encodings, and exact finite physical LOSR implementations of §§66–68, the following minima are attained by common physical channels:

    k=5: minimum branches 2, minimum entropy H(3/5,2/5);
    k=7: minimum branches 3, minimum entropy H(3/7,3/7,1/7).

Here H is the Shannon entropy in bits of the shared branch variable, and the product factors may be arbitrary local CPTP maps C^(2k)→C^k. A single choice of channel acts on all coherent inputs and passive references. Local private randomness is already included in those factors.

The lower bounds are §68's universal packed-weight bounds. It remains to construct orthogonal matrices with column-block squared norms (3/5,2/5) and (3/7,3/7,1/7), respectively. These finite cases complete the packed entropy optimum for every integer 3≤k≤9, using the previously proved cases; they do not imply existence at arbitrary k.

### 69.2 Five fibres from one Fourier pair and its complement

For j=0,...,4 put θ_j=2πj/5 and let T be the 2×5 real matrix with columns

    sqrt(2/5)(cos θ_j, sin θ_j)^T.

The finite Fourier sums Σ_j exp(iθ_j)=Σ_j exp(2iθ_j)=0 imply TT^T=I_2. Every column of T has squared norm 2/5. Choose any three orthonormal rows spanning the orthogonal complement of the row space of T and collect them in U. The stacked matrix O=[U;T] is a real orthogonal 5×5 matrix. Each full column has squared norm one, so every column of U has squared norm 3/5.

Consequently O satisfies §68's equality criterion. Its first block gives unit Bloch vectors sqrt(5/3)U[:,j], with branch weight 3/5. Pad T[:,j] with a zero coordinate and multiply by sqrt(5/2) to obtain the other unit Bloch vectors, with branch weight 2/5. Choosing the eigenbases and their coordinatewise conjugates as in §66 supplies the asserted common two-product-channel implementation.

The existence of an orthonormal complement here is ordinary finite-dimensional orthogonal completion. It is used only once, and its constant column norm follows from the full-column norm identity; no iterative constant-diagonal decomposition theorem is assumed.

### 69.3 Seven fibres from a centered spherical frame

Define

    a=(-1+sqrt(7))/6,    b=(-1−sqrt(7))/6,
    x_0=(0,0,1)^T,
    x_(z,j)=(sqrt(1−z²)cos(2πj/3),
             sqrt(1−z²)sin(2πj/3),z)^T,

for z∈{a,b} and j=0,1,2. Both heights lie in (−1,1), so these are seven real unit vectors. Let X be the 3×7 matrix with these columns, in any fixed order.

The three horizontal directions in each triangle sum to zero. Since a+b=−1/3, the sum of all seven vectors is zero. Moreover a²+b²=4/9. Within each triangle, the sine/cosine first moments and mixed second moment vanish, while the squared cosine and sine sums are both 3/2. Thus

    X X^T = diag((3/2)(2−a²−b²),
                 (3/2)(2−a²−b²),1+3a²+3b²)
          = (7/3) I_3,
    X 1_7=0.

Put R=sqrt(3/7)X and c=(1,...,1)/sqrt(7). The three rows of R and the row c are orthonormal. Choose a 3×7 matrix U whose rows form an orthonormal basis of their orthogonal complement. Then O=[R;U;c] is a real orthogonal 7×7 matrix. Each column of R has squared norm 3/7 and each entry of c has squared norm 1/7, so each column of U has squared norm

    1−3/7−1/7=3/7.

This is exactly the row-block condition of §68. Divide the R and U column blocks by sqrt(3/7); pad the c block with two zeros and divide by sqrt(1/7). The resulting unit Bloch vectors, with weights 3/7,3/7,1/7, define the three common product channels by the conjugate-record construction. All local environments can have dimension two. For the last branch all directions are the same north-pole direction; this is allowed, since distinct fibre input labels are kept orthogonal by their distinct output labels.

In particular, for every pair of different fibres f,g the weighted Bloch inner product is zero because distinct columns of O are orthogonal. Therefore each weighted squared basis overlap is 1/2, for both choices of eigenvector label. Within a fibre the two eigenvectors are orthogonal. These facts verify all encoded matrix units, not only basis populations or a collection of independently chosen pair maps. Hence the implementation remains exact after every passive reference extension.

### 69.4 Completion of the finite range and attribution

Combining these two constructions with §§66–68 gives the following optimal positive-weight distributions for the specified channel:

    k=3: (1);
    k=4: (3/4,1/4);
    k=5: (3/5,2/5);
    k=6: (1/2,1/2);
    k=7: (3/7,3/7,1/7);
    k=8: (3/8,3/8,1/4);
    k=9: (1/3,1/3,1/3).

For k=3 use the three Pauli bases; k=4,8 use §68's scalar Hadamard construction; k=6 uses §66 with a Hadamard matrix of order two; and k=9 uses §67's explicit balanced frame. In every case both the number of listed weights and their Shannon entropy are globally minimal over exact finite physical LOSR decompositions.

The Fourier frame and Naimark-complement principles are standard; see Novikov and Sevost'yanova, Maltsev equal-norm tight frames, §2 and Theorem4, https://www.mathnet.ru/eng/im9137 . The identities X1=0 and XX^T=(7/3)I identify the seven-vector configuration as a centered unit-norm tight frame, equivalently a real spherical2-design; this equivalence is classical, explicitly reviewed in Heineken, Morillas and Tarazaga, Balanced frames: a useful tool in signal processing with good properties, Proposition3.5, https://arxiv.org/html/1904.00920 . The elementary moment computation is supplied above, without a novelty claim for spherical designs or a general projection-decomposition theorem.

The physical resource conclusion uses these standard frame ingredients in the exact common-channel equality criterion. It concerns the stated finite range and fixed MC channel family, with arbitrary physical product competitors and all reference extensions. No general-k existence or positive-error diamond optimum is asserted.

## 70. A quantitative one-product obstruction for four qubit fibres

### 70.1 Unrestricted physical statement

Let F=F_(4,2) be the uniform four-fibre channel of §66. The logical input has labels |f,i>, 1≤f≤4, i∈{0,1}, and the logical output has labels |f>. Its matrix units satisfy

    F(|f,i><f,j|)=δ_ij |f><f|,
    F(|f,i><g,j|)=(1/2)|f><g| for f≠g.

Fix MC encodings J_in(|x><y|)=|xx><yy| and J_out(|f><g|)=|ff><gg|. For arbitrary local CPTP maps A,B:C^8→C^4, define the unhalved diamond error

    δ(A,B)=||(A⊗B)∘J_in−J_out∘F||diamond.

Then

    1/40000 ≤ inf_(A,B) δ(A,B) ≤ 1/2.                    (1)

The lower bound allows arbitrary local ancillas, output populations, extra coherences, and leakage outside the output MC code. It imposes no exact basis-output calibration. The upper bound is attained by an explicit single product channel with error exactly1/2. Two product branches implement the target with zero error by §68's k=4 construction. Formula (1) is a certified interval, not an assertion of the exact one-product optimum.

### 70.2 From actual output error to orthonormal records

It suffices to rule out δ≤1/40000; larger errors already satisfy the lower bound. Fix such a competitor and Stinespring isometries U_A,U_B. For a logical basis state |f,i>, write

    U_A|f,i>=|f>e_(f,i)+b_(f,i),

where b_(f,i) is orthogonal to the output-|f> subspace; use analogous vectors h and c for B. The encoded output and its ideal pure state differ in trace norm at most δ. Since their difference has trace zero, its expectation against any effect has absolute value at most δ/2. Testing the effect |ff><ff| gives

    ||e_(f,i)||² ||h_(f,i)||²≥1−δ/2.

Both factors are at most one, so each is at least1−δ/2. In particular ||b_(f,i)||²,||c_(f,i)||²≤δ/2.

For each fibre let E_f:C²→H_EA have columns e_(f,0),e_(f,1), and let B_f have columns b_(f,0),b_(f,1). Isometry of U_A restricted to that fibre gives

    E_f* E_f=I_2−B_f*B_f,
    0≤B_f*B_f≤δ I_2,

where the second bound follows from its trace≤δ. Since δ<1, the polar-normalized frame V_f=E_f(E_f*E_f)^(-1/2) is an isometry and

    ||E_f−V_f||op≤1−sqrt(1−δ)≤δ.                       (2)

This proves existence of two orthonormal records in the actual environment, even if its dimension was not fixed in advance. On the other party obtain orthonormal frames W_f with the same bound. These auxiliary frames are used to obtain a geometric obstruction; no claim is made that rounding preserves the original physical channel.

### 70.3 Approximate row saturation and a common two-dimensional span

For f≠g, let R_fg and T_fg be the cross-record matrices of the rounded frames, with entries

    R_fg[i,j]=<V_g e_j,V_f e_i>,
    T_fg[i,j]=<W_g e_j,W_f e_i>.

They are 2×2 contractions. The actual retained physical coefficient is <e_(g,j),e_(f,i)><h_(g,j),h_(f,i)>. Its difference from1/2 has modulus at most δ: apply the diamond bound to the trace-norm-one logical matrix unit and then take the indicated output matrix entry. Equation (2) changes each local overlap by at most2δ, hence the product by at most4δ. Therefore

    |R_fg[i,j]T_fg[i,j]−1/2|≤5δ.                        (3)

For every row i, Σ_j|R_ijT_ij|≥1−10δ. Row norms of contractions are at most one, so Cauchy–Schwarz gives each row norm at least1−10δ. Its square is at least1−20δ. Thus Tr(RR*)≥2−40δ and RR*≤I_2 imply

    smallest singular value of R squared≥1−40δ.        (4)

The same row estimate also yields

    Σ_j (|R_ij|−|T_ij|)²
      =||R_i||²+||T_i||²−2Σ_j|R_ijT_ij|≤20δ.

Combining this with (3), and |R_ij|≤1, gives the first-party-only estimate

    ||R_fg[i,j]|²−1/2|≤sqrt(20δ)+5δ.                   (5)

Fix the two-dimensional environment plane S=range(V_1), with orthogonal projection P. For f≠1, the contraction M_f=V_1*V_f has the singular values in (4). Hence

    ||(I−P)V_f||op≤sqrt(40δ).

Its unitary polar factor L_f satisfies ||M_f−L_f||op≤1−sqrt(1−40δ)≤40δ. Set Q_f=V_1 L_f, and Q_1=V_1. All Q_f are orthonormal bases of the same plane S, and

    ||V_f−Q_f||op≤η:=sqrt(40δ)+40δ.                    (6)

For any two unit record vectors, (6) changes their inner product by at most2η and its squared modulus by at most4η. Equation (5) therefore gives, for every distinct f,g and each i,j,

    ||<Q_g e_j,Q_f e_i>|²−1/2|
      ≤(sqrt20+4sqrt40)sqrtδ+165δ=:E(δ).                (7)

All square roots used here are valid under δ≤1/40000<1/40.

### 70.4 Four Bloch axes give a quantitative contradiction

Identify S with C². The first projectors of its four bases have unit Bloch vectors n_1,...,n_4∈R³, and

    |<Q_g e_0,Q_f e_0>|²=(1+n_f·n_g)/2.

Thus (7) implies |n_f·n_g|≤2E(δ). Four unit vectors in R³ must have some pair with absolute inner product at least1/3. Indeed their 4×4 Gram matrix G is positive semidefinite, has rank≤3 and trace4, so Tr(G²)≥16/3 by Cauchy–Schwarz on its nonzero eigenvalues. If all off-diagonal inner products had modulus below1/3, its squared Frobenius norm would be below4+12/9=16/3, a contradiction.

However sqrt20+4sqrt40<30. At δ≤1/40000,

    E(δ)<30/200+165/40000=6165/40000<1/6.

This contradicts the pair lower bound. No product competitor has error≤1/40000; in particular the infimum is at least1/40000, proving the lower side of (1). No compactness argument or exact-output ansatz enters this quantitative conclusion.

### 70.5 A common product attainer for the upper bound

Choose four unit tetrahedral vectors n_f in R³, so n_f·n_g=−1/3 for f≠g; for example use (1,1,1),(1,−1,−1),(−1,1,−1),(−1,−1,1), divided by sqrt3. Let e_(f,i) be eigenvectors of n_f·σ with eigenvalues(-1)^i. Define local isometries

    |f,i>→|f>e_(f,i),
    |f,i>→|f>conjugate(e_(f,i))

on the two parties. They are isometric because within a fibre the records are orthonormal, and different fibres have orthogonal output labels. The product output lies in the MC code, with the correct basis populations and within-fibre units. For f≠g its logical coefficient is

    |<e_(g,j),e_(f,i)>|²
      =1/2−(-1)^(i+j)/6.

To compute its full diamond error, define |f,±>=(|f,0>±|f,1>)/sqrt2 and a CPTP logical compression C with Kraus operators

    K=Σ_f |f><f,−|,    K_f=|f><f,+|  (one for each f).

Their adjoint products sum to I_8. Let D be dephasing in the four output labels and O=id−D. Directly on all matrix units, the difference between this product channel's logical action and F is

    −(1/3) O∘C.

The diamond norm of O is3/2. For the upper bound, let Z=diag(1,i,−1,−i); then D=(1/4)Σ_(j=0)^3 Ad_(Z^j), so the channel triangle inequality bounds ||O||diamond by3/4+3/4=3/2. The uniform pure output state attains3/2, since its difference from I_4/4 has eigenvalues3/4,−1/4,−1/4,−1/4. The normalized input (1/2)Σ_f|f,−> is mapped by C to that uniform pure state. Therefore the product channel's error is exactly1/2, including arbitrary-reference upper control. Isometric MC output encoding preserves this norm.

### 70.6 Attribution and scope

The four-vector Gram estimate is the classical Welch bound in this instance, and the tetrahedral frame, qubit Bloch parametrization and polar decomposition are standard. For the original correlation bound see L. R. Welch, Lower bounds on the maximum cross correlation of signals, IEEE Transactions on Information Theory20 (1974),397–399, https://doi.org/10.1109/TIT.1974.1055219 . For the Gram/frame derivation see also Datta, Howard and Cochran, Geometry of the Welch Bounds, https://arxiv.org/abs/0909.0206 . Channel and diamond facts follow the conventions of Watrous, The Theory of Quantum Information, https://cs.uwaterloo.ca/~watrous/TQI/ . The exact physical target and two-branch zero-error realization are from §§66 and68.

The quantitative step tracks actual wrong-output Stinespring components through record rounding, row saturation and common-span approximation. It establishes a nonzero physical approximation gap between one product channel and two shared branches for this fixed coherent channel, with unrestricted leakage and ancillas. The constants are not asserted sharp, the one-product optimum is not identified, and no arbitrary-channel or full-RT recovery claim is made.

## 71. A robust shared-weight law for uniform qubit fibres

### 71.1 Physical channel and resource statement

Let k≥2 and let F=F_(k,2) be the uniform channel of §66, from a logical input with basis |f,i>, 1≤f≤k and i∈{0,1}, to a logical output with basis |f>. Thus

    F(|f,i><f,j|)=δ_ij |f><f|,
    F(|f,i><g,j|)=(1/2)|f><g|  (f≠g).

Use the fixed MC encodings J_in(|x><y|)=|xx><yy| and J_out(|f><g|)=|ff><gg|. Consider any finite physical LOSR channel

    L=Σ_(t=1)^r w_t (A_t⊗B_t),  w_t>0,  Σ_t w_t=1,

where A_t,B_t map C^(2k) to C^k and are arbitrary CPTP maps. Set

    δ=||L∘J_in−J_out∘F||diamond,
    β(δ)=10δ+18√(20δ),    M_k(δ)=1+(k−1)β(δ).

The diamond norm is unhalved. Local ancillas, populations, extra coherences and leakage outside the output MC code are unrestricted. Every such implementation satisfies

    w_t ≤ min{1, 3M_k(δ)/k}  for every t,                  (1)
    r ≥ ceil(k/[3M_k(δ)]),                                (2)
    H(w) ≥ max{0, log(k/[3M_k(δ)])}.                       (3)

The logarithm in H uses the same arbitrary fixed base greater than one as the logarithm on the right. In particular, the exact shared-weight cap 3/k is stable under physical diamond error, uniformly in the number of branches and all environment dimensions. These are necessary resource bounds; no optimality of their positive-error constants is asserted.

### 71.2 Weighted polar rounding from actual output populations

Choose finite local Stinespring isometries, enlarging each environment to dimension at least two if necessary. For party A write

    U_t|f,i>=|f>e_(t,f,i)+b_(t,f,i),

where b is orthogonal to the output-|f> subspace. Write h and c for party B. Applying the diamond bound to a basis density operator and then the output effect |ff><ff| gives

    Σ_t w_t ||e_(t,f,i)||² ||h_(t,f,i)||² ≥ 1−δ/2.         (4)

The factor δ/2 follows because the difference of the two output density operators is Hermitian and trace zero. Each local good norm is at most one, so (4) implies

    Σ_t w_t ||b_(t,f,i)||² ≤ δ/2,
    Σ_t w_t ||c_(t,f,i)||² ≤ δ/2.                         (5)

For fixed t,f, let E_(t,f) have columns e_(t,f,0),e_(t,f,1), and let B_(t,f) have the two bad columns. Isometry of U_t gives E*E+B*B=I_2. There is an isometry V_(t,f):C²→environment such that

    E_(t,f)=V_(t,f)(E*E)^(1/2),
    ||E_(t,f)−V_(t,f)||op ≤ Tr(B*B).                     (6)

This includes singular E: extend its polar partial isometry on the kernel into the orthogonal complement of its range. The enlarged environment has dimension at least two, so the extension exists. For every singular value s∈[0,1], 1−s≤1−s², which proves (6). No inverse or positive lower singular-value assumption is used. Let H_(t,f) have columns h_(t,f,0),h_(t,f,1), and let W_(t,f) be the corresponding isometry for party B. From (5),

    Σ_t w_t ||E_(t,f)−V_(t,f)||op ≤ δ,
    Σ_t w_t ||H_(t,f)−W_(t,f)||op ≤ δ.                   (7)

These frames are auxiliary mathematical objects, not an assertion that either rounded family is a physical replacement channel.

### 71.3 Approximate cross-Gram saturation in the same mixture

For f≠g define contractions R_(t,fg),T_(t,fg) by

    R_(t,fg)[i,j]=<V_(t,g)e_j,V_(t,f)e_i>,
    T_(t,fg)[i,j]=<W_(t,g)e_j,W_(t,f)e_i>.

The actual output coefficient on |ff><gg| for input |f,i><g,j| is the weighted product of the corresponding unrounded local overlaps. Its difference from 1/2 has modulus at most δ: the input matrix unit has trace norm one and the output matrix coefficient is a norm-one functional. Changing one local overlap to its rounded version costs at most the sum of the two frame errors. Each factor has modulus at most one. Therefore (7) gives

    |Σ_t w_t R_(t,fg)[i,j] T_(t,fg)[i,j]−1/2| ≤ 5δ.      (8)

Fix a row i and omit f,g from the notation. Each row of R_t and T_t has Euclidean norm at most one. Summing the real part of (8) over its two columns gives

    Re Σ_t w_t Σ_j R_t[i,j]T_t[i,j] ≥ 1−10δ.

Consequently,

    Σ_t w_t Σ_j |R_t[i,j]−conj(T_t[i,j])|² ≤ 20δ,         (9)
    Σ_t w_t ||R_t[i,:]||₂² ≥ 1−20δ.                    (10)

For (9), expand the square and bound the two averaged row norms squared by one each. For (10), use Re Σ_j RT ≤ (||Rrow||²+||Trow||²)/2 ≤ (||Rrow||²+1)/2 before averaging. Weighted Cauchy–Schwarz and (9), applied to each entry, now show

    |Σ_t w_t |R_(t,fg)[i,j]|²−1/2| ≤ 5δ+√(20δ).         (11)

Indeed, the difference between Σw RT and Σw |R|² is bounded by (Σw |R|²)^(1/2)(Σw |T−conj(R)|²)^(1/2)≤√(20δ). All averages use the original common branch weights; no pairwise reoptimization has occurred.

### 71.4 A common plane in each branch and a robust Gram bound

Anchor each branch at S_t=range(V_(t,1)), with projection P_t. For f≠1, sum (10) over the two rows of R_(t,1f). This yields

    Σ_t w_t Tr[V_(t,f)*(I−P_t)V_(t,f)] ≤ 40δ.            (12)

Let N_(t,f)=V_(t,1)*V_(t,f), and choose a unitary polar extension L_(t,f) of this 2×2 contraction. Set Q_(t,f)=V_(t,1)L_(t,f), and Q_(t,1)=V_(t,1). Thus each Q is an orthonormal basis of the same plane S_t. If s_1,s_2 are the singular values of N, then

    ||V_(t,f)−Q_(t,f)||F²=2Σ_a(1−s_a)
      ≤2Σ_a(1−s_a²)=2Tr[V_(t,f)*(I−P_t)V_(t,f)].

The identity follows by expanding the Frobenius square and using Re Tr(L*N)=s_1+s_2; it holds also when N is singular. Equation (12) therefore implies

    Σ_t w_t ||V_(t,f)−Q_(t,f)||op ≤ √(80δ).              (13)

Changing the two vectors in a cross overlap changes that overlap by at most their two frame errors. For complex numbers of modulus at most one, the difference of their squared moduli is at most twice their distance. Hence (11) and (13) give, for every f≠g and i,j,

    |Σ_t w_t |<Q_(t,g)e_j,Q_(t,f)e_i>|²−1/2|
      ≤5δ+√(20δ)+4√(80δ)=5δ+9√(20δ).                   (14)

Identify each S_t with C². Let n_(t,f)∈R³ be the unit Bloch vector of the rank-one projector onto Q_(t,f)e_0. The qubit overlap identity and (14) imply

    |Σ_t w_t n_(t,f)·n_(t,g)| ≤ β(δ)  (f≠g).            (15)

Define u_f=(√w_t n_(t,f))_(t=1)^r in the direct sum of r copies of R³, and let U have columns u_f. Its Gram matrix G=U*U has diagonal one and off-diagonal modulus at most β. For every scalar vector x,

    x*Gx ≤ Σ_f |x_f|² + β Σ_(f≠g)|x_f||x_g|
          ≤[1+(k−1)β]||x||₂².

Thus ||U||op²≤M_k(δ). The t-th diagonal 3×3 block of UU* is

    w_t Σ_f n_(t,f)n_(t,f)^T.

It is positive semidefinite, has trace k w_t, and operator norm at most M_k(δ). Its trace is therefore at most 3M_k(δ), proving (1). Summing the weight cap proves (2), while −log w_t≥log(k/[3M_k(δ)]) and H≥0 prove (3).

### 71.5 A positive-error branch obstruction and scope

Fix an integer r with 1≤r<k/3, and define

    a=(k/(3r)−1)/(k−1)>0,    B=18√20.

Every implementation with at most r positive product branches obeys the explicit necessary condition

    δ ≥ [2a/(B+√(B²+40a))]².                            (16)

Indeed, (2) implies M_k(δ)≥k/(3r), hence 10δ+B√δ≥a. Solving this quadratic in √δ, with a rationalized positive root, gives (16). It applies to unrestricted physical channels, all coherent logical inputs and arbitrary reference systems. It does not presume that approximate branches retain exact fibre outputs or a common physical environment plane.

The exact δ=0 cap and its MUB/Bloch resource interpretation are supplied by §66; its classical mutually unbiased basis and traceless-projector ingredients are credited there, including [Boykin, Sitharam, Tiep and Wocjan](https://arxiv.org/abs/quant-ph/0506089) and [Pittenger and Rubin](https://arxiv.org/abs/quant-ph/0308142). The diamond-norm convention is [Watrous, The Theory of Quantum Information, §3.3](https://cs.uwaterloo.ca/~watrous/TQI/). Section 70 treats one product and four fibres with a stronger numerical lower bound and an explicit upper construction. The present theorem supplies a different resource conclusion: simultaneous quantitative control of every shared weight, the branch count and the entropy for arbitrary k and finite mixtures. It asserts no matching positive-error construction or general RT recovery theorem.

## 72. Exact physical calibration reduction for collapsed-fibre channels

### 72.1 Channel class and resource-preserving conclusion

Partition an input basis into k≥2 nonempty fibres X_f of sizes d_f, with N=Σ_f d_f. Let K be an N×N positive semidefinite matrix whose diagonal fibre blocks are K_ff=I_(d_f). Define the channel F_K:C^N→C^k by

    F_K(|f,i><g,j|)=K_(fi,gj)|f><g|.

Its Choi matrix is K on the span of |f,i>_in|f>_out and zero on the orthogonal complement; K≥0 and K_ff=I give complete positivity and trace preservation. Fix the MC encodings J_in(|x><y|)=|xx><yy| and J_out(|f><g|)=|ff><gg|.

For any finite physical LOSR channel L=Σ_t w_t(A_t⊗B_t), with fixed positive weights summing to one and arbitrary local CPTP maps C^N→C^k, there are local CPTP maps A'_t,B'_t with the same weights such that

    A'_t(|f,i><f,j|)=B'_t(|f,i><f,j|)=δ_ij|f><f|,          (1)
    ||Σ_t w_t(A'_t⊗B'_t)J_in−J_out F_K||diamond
       ≤ ||LJ_in−J_out F_K||diamond.                      (2)

The diamond norm is unhalved and includes arbitrary references. Each replacement local map has a Stinespring environment of dimension at most N. Thus exact fibre calibration can be imposed when minimizing error, without restricting the original physical outputs or increasing the number, weights or entropy of shared branches. This is a target-specific error comparison; it does not assert that deleting the diagonal of an arbitrary operator is trace-norm contractive.

Let G denote the compact set of positive semidefinite N×N matrices with diagonal fibre blocks I_(d_f). For any fixed branch weights, the unrestricted physical minimum is exactly

    min_(G_t,H_t∈G)  ν(Σ_t w_t G_t⊙H_t−K),               (3)
    ν(D)=max_(ρ=⊕_f ρ_f≥0, Trρ=1) ||√ρ D √ρ||₁.          (4)

Here ⊙ denotes entrywise product. The finite minimum is attained. The same equality of infima holds for a fixed finite branch budget or weights subject to any prescribed constraint, because the construction preserves the original weights. Attainment holds for fixed weights and for a compact allowed set of weights; no attainment is asserted for arbitrary nonclosed weight constraints. Formula (3) is generally a nonconvex Gram-factor optimization, not a claim of an overall semidefinite program or a solved four-fibre optimum.

### 72.2 Independent local phase twirling

Let Γ=(Z/3Z)^k, ω=exp(2πi/3), D_θ|f,i>=ω^(θ_f)|f,i>, and d_θ|f>=ω^(θ_f)|f>. For each local map set

    A_θ=Ad(d_θ) A Ad(D_θ*),    Abar=|Γ|^(-1)Σ_θ A_θ,

and define Bbar similarly, using independent local phases. The input encoding satisfies

    (Ad(D_θ*)⊗Ad(D_φ*))J_in=J_in Ad(D_(θ+φ)*).

The target is covariant with the corresponding output rotations. Therefore simultaneous conjugation of every branch by the same θ,φ leaves the diamond error of the mixture unchanged. Averaging independently over θ and φ gives Σ_t w_t(Abar_t⊗Bbar_t), whose error is no larger by convexity. This is independent local randomization within each product map, not extra shared branches.

Use input-first Choi matrices. The coordinate |f,i>_in|a>_out has character θ↦ω^(θ_a−θ_f). Zero charge consists of a=f and gives one N×N positive block Q. Each nonzero character e_a−e_f, a≠f, uniquely specifies that ordered pair, and gives a positive d_f×d_f block P_(a,f). Thus the twirled local map is exactly described by

    Q≥0,  P_(a,f)≥0 (a≠f),
    Q_ff+Σ_(a≠f)P_(a,f)=I_(d_f).

Write P_(f,f)=Q_ff. Its full action is

    Abar(|f,i><f,j|)=Σ_a P_(a,f)[i,j]|a><a|,
    Abar(|f,i><g,j|)=Q_fg[i,j]|f><g|  (f≠g).             (5)

These conditions are both necessary and sufficient by Choi positivity and the partial-trace condition. They include arbitrary population leakage and all within-fibre input coherences.

### 72.3 Two local CP repairs and their surviving coefficients

For each branch and each party replace Q by

    Q'=Q+⊕_f(I_(d_f)−Q_ff),                              (6)

and set every nonzero-charge block P_(a,f), a≠f, to zero. Each added block is positive by the completeness relation. Hence Q'≥0 and Q'_ff=I, so (6) defines a CPTP map satisfying (1). The cross-fibre Q_fg are unchanged. Repair both parties this way. For f≠g the effective encoded product coefficient remains Q^A_fg[i,j]Q^B_fg[i,j], whereas all within-fibre effective matrix units become δ_ij|ff><ff|, exactly as in the target.

The Choi rank of the repaired local map is rank Q'≤N, proving the stated finite environment bound. Conversely every G,H∈G gives local maps of this form, and their encoded product is J_out F_(G⊙H). The Schur product theorem supplies positivity; the diagonal fibre blocks remain I.

### 72.4 Reference tags prove the error comparison

Let Δ' be the difference between the repaired mixture and J_out F_K. By the preceding formulas it vanishes on all within-fibre input matrix units and maps every cross-fibre matrix unit to a scalar multiple of |ff><gg|. For a normalized arbitrary pure input with reference R, write

    |ψ>=Σ_(f,i)|f,i>⊗|r_(f,i)>.

Introduce an orthogonal reference tag and define the equally normalized input

    |ψhat>=Σ_(f,i)|f,i>⊗|f>_tag⊗|r_(f,i)>.

The output (Δ'⊗id)(|ψhat><ψhat|) is the isometric embedding of (Δ'⊗id)(|ψ><ψ|) under

    |ff>_out⊗|r> ↦ |ff>_out⊗|f>_tag⊗|r>.

This identity holds for every surviving cross term and hence preserves its entire trace norm, with all input coherences and arbitrary reference vectors retained. Denote the tagged repaired error by C. It is supported on

    S=⊕_f (span{|ff>_out|f>_tag}⊗R).

On the same tagged input, the unrepaired twirled mixture has error C−D+X, where D≥0 is the missing correct-output population supported on S, and X≥0 is supported on S-perpendicular. We now verify these assertions without assuming calibration.

For one branch and fibre put M_f=P^A_(f,f)⊙P^B_(f,f). Both factors are positive contractions, so the Schur product theorem gives

    0≤M_f≤I⊙P^B_(f,f)=diag(P^B_(f,f))≤I.                 (7)

Consequently the correct-output deficit on that fibre is the positive operator

    Σ_(i,j)(I−M_f)[i,j]|r_(f,i)><r_(f,j)|,

placed in output |ff> and tag |f>. Weighted sums of these deficits define D≥0. For any wrong output pair (a,b)≠(f,f), its coefficient matrix is P^A_(a,f)⊙P^B_(b,f)≥0. These positive operators have output |ab> and tag |f>, and are orthogonal to S: equality with a correct sector would require simultaneously a=b=g and f=g, contradicting (a,b)≠(f,f). Their weighted sum is X≥0. Equation (5) shows that every cross-fibre output term is in S and agrees with its repaired value, so no omitted coherence connects S to its orthogonal complement. Trace preservation gives Tr X=Tr D.

The orthogonal supports and the triangle inequality therefore imply

    ||(Δ'⊗id)(|ψ><ψ|)||₁=||C||₁
      ≤||C−D||₁+Tr D
      =||C−D||₁+Tr X
      =||(Δbar⊗id)(|ψhat><ψhat|)||₁
      ≤||Δbar||diamond.                                 (8)

Here Δbar is the twirled original error. For a Hermiticity-preserving map the diamond norm is maximized on a pure state with a reference; alternatively mixed input states follow by convexity and purification. Taking the supremum in (8), and then using the twirling comparison, proves (2).

### 72.5 Exact reference norm and finite attainment

For any Hermitian block matrix D with D_ff=0, define Ψ_D(|f,i><g,j|)=D_(fi,gj)|f><g|. The same tagging argument preserves the output error norm for every pure input. Let T_f have columns r_(f,i) and set T=⊕_f T_f, viewing its ranges as mutually orthogonal reference-tag sectors. The tagged output, after identifying each correct output/tag sector with its reference space, is exactly T D T*. Normalization says Σ_f Tr(T_f*T_f)=1. Polar decomposition of each T_f, with harmless reference padding if needed, shows

    ||T D T*||₁=||√ρ D √ρ||₁,    ρ=⊕_f T_f*T_f.

Conversely any block-diagonal density matrix ρ is realized by taking T_f=√ρ_f on orthogonal reference sectors. This proves ||Ψ_D||diamond=ν(D), and the output encoding J_out preserves that norm. Combining this with the repaired Gram masks proves (3)–(4).

Each G∈G has trace N and bounded entries, so G is compact. The diamond norm is continuous in its finite-dimensional map coefficients. Thus the minimum in (3) exists and is physically realized by the finite local Choi factors already constructed. Allowing at most r branches uses the compact probability simplex, with zero-weight branches discarded; it does not require a limit with unbounded shared support.

### 72.6 A quantitative four-fibre consequence

For the uniform four-fibre qubit target of §70, reduction (2) allows restriction to calibrated products with arbitrary environments. Let δ be the error of such a product and let R_fg,T_fg be its two 2×2 cross-Gram contractions. Actual matrix-unit coefficients give |R_fg[i,j]T_fg[i,j]−1/2|≤δ. For each row, expansion and Cauchy–Schwarz as in §71 give

    Σ_j|R_fg[i,j]−conj(T_fg[i,j])|²≤4δ,
    ||R_fg[i,:]||₂²≥1−4δ,
    ||R_fg[i,j]|²−1/2|≤δ+2√δ.                            (9)

Anchor the first party's orthonormal frames at the first fibre. Summing the middle estimate in (9) over two rows bounds each other frame's squared residual outside the anchor plane by 8δ. A unitary polar extension on that plane therefore gives a common-plane orthonormal frame at Frobenius distance at most 4√δ, including singular overlap cases. Changing two frames changes each squared cross overlap by at most 16√δ. Thus the four corresponding unit Bloch vectors obey

    |n_f·n_g|≤2δ+36√δ  (f≠g).

Their 4×4 Gram matrix has rank at most three and trace four, so Tr G²≥16/3. Its four diagonal squares sum to four, forcing some off-diagonal modulus to be at least 1/3. Therefore

    δ+18√δ≥1/6,
    δ≥[1/(3(18+√(324+2/3)))]².                          (10)

The same bound holds for every original unrestricted product by (2). Together with §70's explicit tetrahedral product, the one-product optimum lies between the number in (10), approximately 8.56×10^(-5), and 1/2. The lower value improves §70's 1/40000 but is not claimed optimal; the principal conclusion is the exact resource-preserving reduction for the entire collapsed-fibre channel class.

The Choi, Schur-product and Hermiticity-preserving diamond facts used here are standard; see [Watrous, The Theory of Quantum Information, §§2.2,3.3,4.1.3](https://cs.uwaterloo.ca/~watrous/TQI/) and [Watrous, Simpler semidefinite programs for completely bounded norms](https://arxiv.org/abs/1207.5726). Sections 54 and 63–65 describe exact-support Gram constructions; §§70–71 retain unrestricted physical leakage in quantitative obstructions. The reduction above compares unrestricted approximation with calibrated implementations at the same shared resource by a reference-tagged trace-compensation argument. It asserts no general diagonal-repair contraction, no four-fibre exact optimum and no arbitrary-channel or full-RT theorem.

## 73. A qutrit-environment product beating the tetrahedral approximation

### 73.1 Statement and precise comparison class

For the uniform four-fibre qubit channel F_(4,2) with the fixed MC input and output encodings of §§66 and 70, there exists a single physical product CPTP channel whose unhalved diamond error is strictly less than 1/3. It uses local Stinespring environments of dimension three and exactly calibrates the fibre outputs. In particular, the tetrahedral product's error 1/2 is not the unrestricted one-product optimum.

There is also an exact restricted comparison: among calibrated products constructed from four orthonormal qubit-environment bases on one party and their entrywise conjugates on the other party, the minimum error is 1/2. Thus the construction below strictly improves this entire conjugate-paired, common-qubit-environment class. No lower bound of 1/2 is asserted for arbitrary unequal local frames, and the unrestricted optimum is not determined.

### 73.2 Explicit rational local isometries

Let I denote the 3×3 identity and define Hermitian integer matrices

    A_1 = 0,

    A_2 = [[ 5,       −2+14i,  8−3i ],
           [−2−14i,  −6,     −1+4i ],
           [ 8+3i,   −1−4i,   3    ]],

    A_3 = [[−4,        12+10i, −5−3i ],
           [12−10i,    14,      5+2i ],
           [−5+3i,      5−2i, −11    ]],

    A_4 = [[ 1,       −5−12i,  1+7i ],
           [−5+12i,    3,      3+4i ],
           [ 1−7i,     3−4i,  −4    ]].

Set H_f=A_f/32 and U_f=(I+iH_f)(I−iH_f)^(-1). Since H_f is Hermitian, I−iH_f is invertible and U_f is unitary. All entries are Gaussian rationals. Let v_(f,0),v_(f,1) be its first two columns. Define local Stinespring isometries by

    V_A|f,j>=|f>⊗v_(f,j),
    V_B|f,j>=|f>⊗conj(v_(f,j)).

Within each fibre the two records are orthonormal, while distinct output labels are orthogonal. Hence these formulas define isometries on the entire eight-dimensional local input. Trace out their three-dimensional environments to obtain A and B. For f≠g, the encoded output coefficient on |ff><gg| is

    C_(fi,gj)=|<v_(f,i),v_(g,j)>|²,

and within each fibre it is δ_ij. Thus this is one common physical product implementation on every coherent input, not a collection of pairwise maps.

Let V be the 3×8 concatenation of the selected columns, Q=V*V, and let K be the target kernel with K_ff=I₂ and K_fg=J₂/2 for f≠g. Define the real symmetric rational matrix

    D=Q⊙conj(Q)−K.

Its diagonal 2×2 blocks vanish. The full encoded channel difference is the collapsed-fibre map with kernel D, followed by the output MC isometry.

### 73.3 An exact rational full-reference certificate

Define Z=M/10000, where

    M = [[1576, 235, 359, 589, 678, 951, 947, 210],
         [ 235, 283, 110, 171, 124, 147,−234, 459],
         [ 359, 110,3128,  42, 918, −62, 806, 109],
         [ 589, 171,  42,3010, −39, 711,  33, 993],
         [ 678, 124, 918, −39,3036,−189, 670,  74],
         [ 951, 147, −62, 711,−189,3168, −30, 725],
         [ 947,−234, 806,  33, 670, −30,2998,−111],
         [ 210, 459, 109, 993,  74, 725,−111,3197]].

The following exact rational inequalities certify the desired bound:

    Z−D>0,  Z+D>0,
    I₂/3−Z_ff>0  for f=1,2,3,4.                          (1)

For completeness, they can be verified without eigenvalue approximation by the scalar LDL recurrence. For any real symmetric matrix B, put L_jj=1 and recursively

    p_j=B_jj−Σ_(h<j)L_jh² p_h,
    L_ij=(B_ij−Σ_(h<j)L_ih L_jh p_h)/p_j  (i>j).

Substitute the displayed rational matrices, with D defined by the rational Cayley inverses above. Every pivot exceeds the corresponding positive rational lower bound in the following lists; every listed integer is divided by 10^6:

    B=Z−D: 157599,24794,123304,5523,1753,1884,1498,1391;
    B=Z+D: 157599,24794,215316,281499,137603,23444,3121,2938;
    B=I₂/3−Z_11: 175732,301889;
    B=I₂/3−Z_22: 20532,31473;
    B=I₂/3−Z_33: 29732,4518;
    B=I₂/3−Z_44: 33532,9958.

These are finite rational inequalities, obtained by the stated recurrence; positivity of all pivots proves (1) by B=L diag(p_j)L^T.

To see why (1) controls arbitrary references, use the exact reference norm of §72:

    ||(A⊗B)J_in−J_out F_(4,2)||diamond
      =max_(ρ=⊕_fρ_f≥0,Trρ=1)||√ρ D √ρ||₁.

From Z≥±D, the Hermitian matrix √ρD√ρ lies between ±√ρZ√ρ. Resolving its positive and negative spectral subspaces gives

    ||√ρD√ρ||₁≤Tr(ρZ)
      ≤max_f λ_max(Z_ff)<1/3.

This proves the claimed strict full-reference upper bound. The positive-definite certificate gives a uniform margin; no numerical optimizer output or numerical eigenvalue is used as a premise of this bound.

### 73.4 Why every conjugate-paired qubit environment costs at least one half

Consider any four orthonormal bases v_(f,0),v_(f,1) in C², with conjugate records on the other party. Let n_f∈R³ be the unit Bloch vector of |v_(f,0)><v_(f,0)|. Their retained cross coefficients are

    C_(fi,gj)=[1+(−1)^(i+j)n_f·n_g]/2  (f≠g).

Take the normalized logical input

    |ψ>=(1/2)Σ_(f=1)^4 |f,−>,
    |f,−>=(|f,0>−|f,1>)/√2.

The difference between the physical and target outputs, after identifying the output MC code with C⁴, is (G−I₄)/4, where G_fg=n_f·n_g. This follows by summing the four internal signs for each cross-fibre block; all diagonal output errors vanish. The Gram matrix G is positive semidefinite, has trace four and rank at most three. Hence G−I₄ has trace zero and an eigenvalue −1, so its trace norm is at least two. This input already gives diamond error at least 1/2. Section 70's tetrahedral bases attain 1/2, proving the exact restricted optimum.

The qutrit-environment construction above therefore shows that imposing a common qubit environment with conjugate records can change the one-product approximation optimum. It neither settles the optimum over all qubit-environment products nor the unrestricted optimum.

The Gram, Schur-product and diamond-order ingredients are standard and credited in §§54 and 72 and in [Watrous, The Theory of Quantum Information](https://cs.uwaterloo.ca/~watrous/TQI/). The displayed finite channel and rational certificate supply the strict counterexample to tetrahedral optimality for this fixed coherent target. No general RT recovery claim is made.

## 74. A Kraus-rank obstruction and a sharp qubit-environment threshold

### 74.1 Uniform fibres and the rank resource law

Let k,d≥2. The uniform collapsed-fibre channel F_(k,d):C^(kd)→C^k has matrix units

    F_(k,d)(|f,i><f,j|)=δ_ij|f><f|,
    F_(k,d)(|f,i><g,j|)=(1/d)|f><g|  (f≠g).

Use the fixed output MC isometry J_out(|f><g|)=|ff><gg| and write T=J_out F_(k,d). For any CPTP map C:C^(kd)→C^k⊗C^k with Kraus rank at most k(d−1),

    ||C−T||diamond ≥ 2/k.                                (1)

The diamond norm is unhalved. The competitor C need not preserve the output code, calibrate basis outputs, have a product structure, or satisfy any covariance. All coherences, output leakage and reference systems are included.

For a physical finite LOSR implementation L=Σ_t w_t(A_t⊗B_t), with fixed MC input encoding J_in and positive weights, let a_t,b_t be the local Kraus ranks, equivalently the minimal pure Stinespring environment dimensions. Then

    Σ_t a_t b_t ≤ k(d−1)
      implies ||LJ_in−T||diamond ≥ 2/k.                   (2)

In particular, error strictly below 2/k requires Σ_t a_t b_t≥k(d−1)+1. If r branches all have local Kraus ranks at most a,b, the necessary condition is rab≥k(d−1)+1. This is a joint branch-and-environment budget, not a replacement for the exact shared-weight law of §66.

For k=4,d=2 the optimum over all CPTP competitors of Kraus rank at most four is exactly 1/2. The same exact optimum holds for all single physical product channels whose two local Kraus ranks are at most two. The lower bounds allow arbitrary unequal, nonconjugate local maps and arbitrary output leakage. Section 70's tetrahedral product attains 1/2 with two-dimensional local Stinespring environments. Section 73's three-dimensional local-environment product has error strictly below 1/3. These facts give an actual auxiliary-dimension separation, not merely a separation within the calibrated conjugate-paired class.

The environment dimension in these statements is that of a pure Stinespring dilation. A mixed ancillary implementation must include its purification when translated into this resource; the bare dimension of an unpurified mixed ancilla is not the Kraus rank.

### 74.2 Target Choi support and a kernel witness

Use the unnormalized input-first Choi convention

    J(C)=Σ_(x,y)|x><y|⊗C(|x><y|),
    Tr_out J(C)=I_(kd).

Let u=d^(-1/2)(1,...,1) in C^d and let j_k be the all-ones vector in C^k. On the span of |f,i>_in|ff>_out, the target Choi matrix is isometrically identified with

    K=I_k⊗(I_d−uu*) + j_k j_k*⊗uu*.

It is zero on the orthogonal complement of that span. Hence its nonzero eigenvalues are k once and 1 with multiplicity k(d−1). In particular,

    dim S=k(d−1)+1,  S=range J(T),
    <x,J(T)x>≥||x||²  for x∈S.                           (3)

If rank J(C)≤k(d−1), restricting J(C) to the subspace S has a nontrivial kernel by rank-nullity. Thus there is nonzero

    x∈S∩ker J(C).

Since S lies in the displayed target-coordinate span, x can be written uniquely as

    x=Σ_f x_f⊗|ff>,   x_f∈span{|f,i>:1≤i≤d}.

The input vectors x_f live in mutually orthogonal fibre spaces. Put n_f=||x_f|| and s=Σ_f n_f>0.

### 74.3 A normalized singular input density gives the factor two

For each n_f>0 set q_f=x_f/n_f and p_f=n_f/s. Define the input-first density operator

    ρ=Σ_(f:n_f>0) p_f |q_f><q_f|.

It has trace one; zero components are omitted. It is generally singular. Let A=√ρ⊗I_out and use the inverse square root only on the support of ρ. Since x lies in range A, the vector

    y=(ρ^(-1/2) on its support ⊗I_out)x

is well defined and satisfies Ay=x. Orthogonality of the output labels and of the input fibres gives

    ||y||²=Σ_(f:n_f>0) n_f²/p_f=s².

Write z=y/s, a unit vector. Let Δ=C−T and Y=A J(Δ) A. This is an actual output difference on a normalized input with reference. Explicitly, in the fixed input basis take

    |ψ_ρ>=Σ_x (√ρ|x>)_R⊗|x>_in.

Its squared norm is Trρ=1 and

    (id_R⊗Δ)(|ψ_ρ><ψ_ρ|)
       =(√ρ⊗I_out)J(Δ)(√ρ⊗I_out)=Y.                    (4)

The input marginal is ρ^T in this convention; no replacement of ρ by an unmentioned transpose is needed. Both terms in (4) are normalized output states. Thus Y is Hermitian with trace zero and ||Y||₁≤||Δ||diamond. The kernel property gives

    <z,Yz>=−<x,J(T)x>/s²<0.

For a Hermitian trace-zero operator, the trace norm is twice the trace of its negative part. Its negative part has trace at least −<z,Yz> for any unit z with negative expectation. Therefore

    ||C−T||diamond ≥2<x,J(T)x>/s²
      ≥2Σ_f n_f²/(Σ_f n_f)²
      ≥2/k.                                             (5)

The last step is Cauchy–Schwarz. Equations (3)–(5) prove (1) without calibration, twirling, diagonal repair, or restrictions on where the competitor's Choi support lies.

### 74.4 Physical rank budgets and exact four-fibre attainment

Choose local Kraus families with a_t and b_t operators. Their tensor products give a_t b_t Kraus operators for A_t⊗B_t. Precomposing with the fixed input MC isometry cannot increase this count. Multiplying by √w_t and concatenating across branches gives a Kraus family of size Σ_t a_t b_t for LJ_in. This proves (2) from (1), regardless of linear dependence between the displayed Kraus operators.

At k=4,d=2, every pair of local channels admitting pure two-dimensional Stinespring environments has local Kraus ranks at most two, so its effective encoded channel has Kraus rank at most four. Equation (1) gives error at least 1/2 for all such products. The tetrahedral construction of §70 uses exactly such local environments and has full-reference error 1/2, so the lower bound is attained. That same example belongs to the larger class of all effective CPTP maps of Kraus rank at most four; consequently the minimum over that larger class is also 1/2.

The rational qutrit-environment product of §73 has error below 1/3 and therefore cannot have effective Choi rank at most four. Its improvement over all two-dimensional-local-environment products is strict. No optimality of its particular error, no classification of mixed budgets such as (2,3), and no equality claim for (1) at all k,d are asserted.

### 74.5 Attribution and boundary of the conclusion

Kraus rank, Choi rank and minimal pure Stinespring environment dimension are standard equivalent channel resources; see [Watrous, The Theory of Quantum Information, §§2.2 and 3.3](https://cs.uwaterloo.ca/~watrous/TQI/). The general obstruction to strong channel approximation by much smaller Kraus rank is established background: [Lancien and Winter, Approximating quantum channels by completely positive maps with small Kraus rank, Quantum 8,1320 (2024), §2](https://quantum-journal.org/papers/q-2024-04-30-1320/) explicitly distinguishes diamond approximation from unreferenced output-state approximation and notes the Choi-rank obstruction. The present argument uses the uniform fibre target's support and an adapted normalized reference input to obtain the explicit 2/k bound and the sharp four-fibre resource threshold. It does not claim that the general rank-obstruction principle is new.

Unlike §72's calibration reduction, which preserves shared weights but may enlarge local environments, this proof acts directly on the original effective Choi matrix. It therefore supports the stated dimension-restricted conclusion even for leakage-bearing and nonconjugate competitors. The unrestricted one-product optimum with no environment bound remains open.

## 75. Growing only one local environment beats the two-qubit threshold

### 75.1 The asymmetric resource threshold

Use the four-fibre, two-dimensional-fibre channel F_(4,2) of §§66 and 74, with fixed MC input and output encodings. Its logical input basis is |f,i>, where 1≤f≤4 and i∈{0,1}, and

    F_(4,2)(|f,i><f,j|)=δ_ij|f><f|,
    F_(4,2)(|f,i><g,j|)=(1/2)|f><g|  for f≠g.

There is a single physical product channel A⊗B, with local Kraus ranks exactly two and three respectively, whose encoded unhalved diamond error from J_out F_(4,2) is strictly below 3/8. Exchanging the parties gives the same statement for ranks (3,2).

By §74, every physical product with both local Kraus ranks at most two has error at least 1/2, with equality attained by the tetrahedral product. Consequently, if one side is allowed local Kraus rank at most two, increasing the other side's bound from two to three is necessary and sufficient to permit error strictly below 1/2. This is an environment-resource threshold, not a formula for the optimum at budget (2,3). All competitors in the lower statement may have leakage and unequal, nonconjugate local maps. The explicit upper construction below calibrates the basis outputs, which is a valid construction rather than an assumption on those competitors.

More generally, among all physical product channels with these fixed local input and output dimensions, the minimum product of the two local Kraus ranks permitting error strictly below 1/2 is exactly six. It is attained at (2,3) or (3,2).

Local environment dimensions mean pure Stinespring dimensions, equivalently local Kraus ranks. No statement about bare unpurified mixed-ancilla dimensions is intended.

### 75.2 Exact local isometries

For a Hermitian matrix H define its Cayley unitary

    U(H)=(I+iH)(I−iH)^(-1).

The inverse exists because H has real spectrum. Commutation of the two polynomial factors gives U(H)*U(H)=I.

Let A_1=0_(2×2), B_1=0_(3×3), and set

    A_2=[[-15,17+9i],[17−9i,−6]],
    A_3=[[-1,19+22i],[19−22i,−37]],
    A_4=[[2,−2−14i],[−2+14i,8]],

    B_2=[[14,−13+6i,−10+4i],
         [−13−6i,7,−4+8i],
         [−10−4i,−4−8i,4]],
    B_3=[[-2,−12+19i,1+10i],
         [−12−19i,37,−7+2i],
         [1−10i,−7−2i,−2]],
    B_4=[[-4,3−18i,6−8i],
         [3+18i,−11,10i],
         [6+8i,−10i,7]].

Define a_(f,i)=U(A_f/32)e_i in C² and b_(f,i)=U(B_f/32)e_i in C³, using the first two columns in the latter case. Each fibre therefore gives an orthonormal pair of local records. In fixed computational bases define local isometries from C⁸ by

    V_A|f,i>=|f>⊗overline(a_(f,i)),
    V_B|f,i>=|f>⊗overline(b_(f,i)).

Orthogonality of the output labels and of each record pair proves V_A*V_A=V_B*V_B=I_8. Tracing the respective record spaces defines CPTP maps A:C⁸→C⁴ and B:C⁸→C⁴, with Kraus ranks at most two and three. No shared randomness is used.

Let G_A and G_B be the 8×8 Gram matrices of the un-conjugated columns a_(f,i) and b_(f,i), in the order (1,0),(1,1),...,(4,0),(4,1). The explicit complex conjugates in V_A,V_B fix the coefficient convention: tracing the records on |f,i><g,j| gives (G_A)_(fi,gj)(G_B)_(fi,gj), with no additional transpose.

After the physical MC input encoding, both output labels agree. The resulting logical channel has coefficient matrix G_A⊙G_B. Let K have diagonal 2×2 blocks I₂ and off-diagonal blocks J₂/2, and put

    D=G_A⊙G_B−K.

Thus D is Hermitian, its diagonal fibre blocks vanish, and the physical channel difference is the MC output embedding of the collapsed-fibre coefficient map D. These identities specify its action on all 64 input matrix units, including coherent cross-fibre inputs.

### 75.3 A literal rational certificate

The following Hermitian matrix Z=(R+iS)/10000 is a certificate for the entire channel difference:

    R=[[3324,−180,664,−877,806,322,871,−719],
       [−180,2843,304,753,−57,1073,−136,816],
       [664,304,2460,−144,782,225,1320,358],
       [−877,753,−144,3598,−803,662,−60,609],
       [806,−57,782,−803,3616,−45,494,−930],
       [322,1073,225,662,−45,2854,222,991],
       [871,−136,1320,−60,494,222,3274,−147],
       [−719,816,358,609,−930,991,−147,3374]],

    S=[[0,157,205,530,671,−353,−293,596],
       [−157,0,−234,1036,508,100,67,−433],
       [−205,234,0,4,104,534,−176,−377],
       [−530,−1036,−4,0,−266,137,430,322],
       [−671,−508,−104,266,0,95,809,191],
       [353,−100,−534,−137,−95,0,−233,649],
       [293,−67,176,−430,−809,233,0,230],
       [−596,433,377,−322,−191,−649,−230,0]].

All entries of D and Z are Gaussian rational numbers. Direct exact elimination gives

    Z−D>0,  Z+D>0,
    (3/8)I₂−Z_ff>0  for f=1,2,3,4.                    (1)

For an explicit reproducible positivity check, use the ordinary Hermitian LDL* elimination without pivoting. If M=L diag(p_1,...,p_n)L*, with unit diagonal in L, its recursion is

    p_j=M_jj−Σ_(h<j)|L_jh|²p_h,
    L_ij=(M_ij−Σ_(h<j)L_ih p_h overline(L_jh))/p_j.

The following integers are strict lower bounds for 10⁶ times the successive exact rational pivots:

    Z−D: 332399,282582,5553,16199,4216,2071,1765,1489;
    Z+D: 332399,282582,167838,100819,22930,37115,2394,3241;
    (3/8)I₂−Z_11: 42599,77307;
    (3/8)I₂−Z_22: 128999,13590;
    (3/8)I₂−Z_33: 13399,81352;
    (3/8)I₂−Z_44: 47599,21945.

Every listed bound is positive, so the recursion proves (1) using rational arithmetic. The matrices above, rather than rounded eigenvalues or a numerical optimizer, determine the certificate.

### 75.4 Full-reference diamond bound and resource consequence

For completeness, the coefficient norm from §72 can be used directly here. On any normalized pure input with arbitrary reference write

    |ψ>=Σ_(f,i)|f,i>⊗r_(f,i),
    T_f e_i=r_(f,i),  ρ=direct_sum_f(T_f*T_f).

Then ρ is block diagonal, positive semidefinite and has trace one. After identifying the MC output isometrically with C⁴, the output difference is TDT*, where T=direct_sum_f T_f maps into direct_sum_f R. Polar decomposition, including singular blocks, gives

    ||TDT*||₁=||√ρ D √ρ||₁.

Since −Z≤D≤Z, the trace-norm dual bound gives

    ||√ρ D √ρ||₁≤Tr(ρZ)
      =Σ_f Tr(ρ_ff Z_ff)
      ≤max_f λ_max(Z_ff)<3/8.                           (2)

For example, the first inequality follows by writing the positive and negative spectral projections of √ρD√ρ and applying the two operator inequalities separately. The last strict inequality follows from all four strict 2×2 inequalities in (1), so its margin is uniform over all input states and all references. The standard pure-input characterization of the diamond norm for Hermiticity-preserving channel differences now proves the asserted bound. Isometric MC output embedding preserves this norm.

If either local Kraus rank in this construction were smaller than its stated value two or three, their product would be at most four. Section 74 would then force error at least 1/2, contradicting (2). Thus the two local Kraus ranks are exactly two and three. Exchanging the parties exchanges their resource dimensions without changing G_A⊙G_B or the error.

For any local CPTP map C⁸→C⁴, a pure Stinespring isometry C⁸→C⁴⊗C^a requires 8≤4a. Therefore each local Kraus rank is an integer at least two. If the product ab is smaller than six, it must be four, with a=b=2; §74 then rules out error below 1/2. The displayed ranks (2,3) attain error below 3/8, so the minimum product resource for beating 1/2 is exactly six. This argument uses the fixed full local input and output dimensions, not only their encoded subspaces.

The lower bound for budget (2,2) comes directly from §74 applied to the original effective Choi matrix. No dimension-preserving use of the calibration theorem is made. The threshold conclusion therefore concerns actual original physical channels, even though the upper witness happens to be calibrated.

### 75.5 Attribution and scope

Cayley unitary parametrization, Stinespring dilations and positive-semidefinite trace-norm certificates are standard linear algebra and channel theory; see [Watrous, The Theory of Quantum Information, §§2.2 and 3.3](https://cs.uwaterloo.ca/~watrous/TQI/) and [Watrous, Simpler semidefinite programs for completely bounded norms, §3.2](https://arxiv.org/abs/1207.5726). Sections 72 and 73 supply the block-Gram channel norm and the earlier symmetric qutrit-environment certificate; §74 supplies the unrestricted small-rank obstruction. The present finite asymmetric construction establishes that only one environment needs to grow to beat the sharp two-qubit-environment threshold. It does not determine the exact optimum at budget (2,3), establish error below 1/3 at that budget, or determine the unrestricted-environment one-product optimum.

## 76. A nonlinear Schmidt-support obstruction to one-product recovery

### 76.1 Uniform qubit fibres and the quantitative conclusion

For the uniform collapsed-fibre channel F_(k,2), let k≥4. The fixed MC input encoding sends |f,i> to |f,i>_A|f,i>_B, and the output encoding sends |f> to |ff>. Local physical channels have full input dimension 2k and output dimension k. For every single product of CPTP maps A⊗B, define the unhalved error

    δ=||(A⊗B)J_in−J_out F_(k,2)||diamond.

No environment bound, covariance, calibrated outputs or leakage restriction is imposed. Then

    δ≥max{(sqrt(16k−39)−3)/(4k), 2(k−3)/(5k)}.           (1)

In particular, the unrestricted one-product optimum for the four-fibre target is at least 1/8. Together with §73's explicit product, it lies in [1/8,1/3). This does not identify that optimum. The general lower bound has limit at least 2/5 as k grows.

The mechanism is nonlinear: two coherent test inputs force incompatible properties of one common family of environment records. A single linear functional cannot strictly separate this target from every product channel, because §66 supplies an exact finite LOSR realization.

### 76.2 A rank-two Schmidt-support inequality

Let a_0,a_1 and b_0,b_1 be orthonormal pairs in arbitrary finite-dimensional local spaces. Set

    x_i=a_i⊗b_i,
    c=(x_0+x_1)/sqrt(2),
    d=(x_0−x_1)/sqrt(2).

These are orthonormal unit vectors. Their two local reduced density operators are equal: both are the uniform states on the spans of the corresponding record pairs.

Let c₀ be any maximally entangled rank-two unit vector, with local Schmidt-support projections P_A,P_B. Write

    P=P_A⊗P_B,
    Q=P−|c₀><c₀|,
    F=|<c₀,c>|²,  e=1−F.

Here Q is an orthogonal projection of rank three. Then

    ||(I−Q)d||²≤e+e².                                  (2)

To prove this, write F_−=|<c₀,d>|² and p_±=<c or d,P(c or d)>. Every product vector a⊗b satisfies

    |<c₀,a⊗b>|²≤(1/2)||P_A a||²||P_B b||².

Applying this to x_0,x_1 and using the plus/minus change of basis gives

    F+F_−≤(p_++p_−)/2.

Let h_A=<a_0,P_A a_1> and h_B=<b_0,P_B b_1>. Direct expansion gives p_+−p_−=2 Re(h_A h_B). Consequently

    <d,Qd>=p_−−F_−≥F−Re(h_A h_B)≥F−|h_A h_B|.          (3)

For L_A=Σ_i||(I−P_A)a_i||², orthogonality of a_0,a_1 gives

    |h_A|=|<a_0,(I−P_A)a_1>|≤L_A/2.

Moreover, |c₀><c₀|≤P_A⊗I and the local reduced-state identity imply F≤1−L_A/2. Thus L_A≤2e. The same statements hold for B, so |h_A h_B|≤e². Substituting into (3) proves (2).

The simpler coefficient-one bound ||(I−Q)d||²≤e is false. In local dimension three take

    c₀=(|00>+|11>)/sqrt(2),
    a_0=b_0=(e_0+e_2)/sqrt(2),
    a_1=b_1=(e_0−e_2)/sqrt(2).

Then c=(|00>+|22>)/sqrt(2), d=(|02>+|20>)/sqrt(2), F=1/4, and Qd=0. The leakage is one although e=3/4. No optimality of the quadratic estimate (2) is asserted.

### 76.3 Two normalized coherent tests select an actual anchor

By §72's resource-preserving calibration theorem, any original product has a calibrated product replacement of no greater diamond error. It suffices to prove (1) for that replacement; for the remainder of the proof let δ denote its error. This reduction preserves the number of product branches, and no claim about preservation of its original environment dimensions is needed here.

A calibrated product has local Stinespring records a_(f,0),a_(f,1) and b_(f,0),b_(f,1), orthonormal within each fibre, with unrestricted common local environment spaces. Put

    x_(f,i)=a_(f,i)⊗b_(f,i),
    c_f=(x_(f,0)+x_(f,1))/sqrt(2),
    d_f=(x_(f,0)−x_(f,1))/sqrt(2).

Let C and M be their k×k Gram matrices, C_fg=<c_f,c_g> and M_fg=<d_f,d_g>. Each c_f and d_f is a unit vector; within each fibre c_f is orthogonal to d_f. Define the two normalized logical input states

    |ψ_±>=k^(-1/2)Σ_f |f,±>,
    |f,±>=(|f,0>±|f,1>)/sqrt(2).

After the output MC isometry is removed, the actual outputs are C^T/k and M^T/k respectively. The transpose comes from tracing the environment in the convention Gram_fg=<record_f,record_g>. The ideal outputs are J_k/k and I_k/k. Transposition preserves trace norm, so

    δ≥||C−J_k||₁/k,
    δ≥||M−I_k||₁/k.                                   (4)

These tests need no reference, but their errors are lower bounds for the full-reference diamond norm. All four output operators in (4), divided by k as displayed, are normalized density matrices. This normalization supplies the trace-zero factor two used below.

Let c̄=k^(-1)Σ_f c_f. Testing the first output difference against the pure uniform state gives

    2(1−||c̄||²)≤δ.                                    (5)

Indeed the difference has trace zero, and the ideal uniform-state expectation is one. Set σ=k^(-1)Σ_f|c_f><c_f|. The Gram representation gives λ_max(σ)≥||c̄||². Since 0≤δ≤2 for channel differences, (5) implies

    Trσ²≥λ_max(σ)²≥(1−δ/2)²≥1−δ.

Average over actual fibre indices a:

    (1/k)Σ_a Σ_f (1−|<c_a,c_f>|²)
       =k(1−Trσ²)≤kδ.

Therefore some actual c_a, still maximally entangled of Schmidt rank two, satisfies

    s:=Σ_f e_f≤kδ,
    e_f:=1−|<c_a,c_f>|²∈[0,1].                         (6)

The anchor is c_a, not the mean c̄; no Schmidt-rank assertion about the mean is made.

### 76.4 Common three-dimensional support forces a spectral deficit

Let Q be the rank-three projection associated with this anchor c_a as in (2). Applying the support inequality to every pair c_f,d_f gives

    Σ_f||(I−Q)d_f||²≤Σ_f(e_f+e_f²)
      ≤s+min{s²,s}
      ≤min{kδ+k²δ²,2kδ}.                               (7)

Let B:C^k→H_A⊗H_B have columns d_f, so M=B*B. The positive matrix B*QB has rank at most three. The sum of the k−3 smallest eigenvalues of M is at most

    Tr B*(I−Q)B=Σ_f||(I−Q)d_f||².                      (8)

For example, choose a (k−3)-dimensional subspace of ker(QB) and apply the variational characterization of the sum of the smallest eigenvalues; the trace of B*(I−Q)B on that subspace is bounded by its full trace. This argument neither assumes a common local Schmidt plane for all fibres nor truncates the competitors' environments.

Write the eigenvalues of M increasingly as λ_1,...,λ_k. Since TrM=k, the second trace-zero difference in (4) yields

    δ≥(2/k)Σ_j(1−λ_j)_+
      ≥(2/k)((k−3)−Σ_(j=1)^(k−3)λ_j).                 (9)

Combining (7)–(9) separately with its two bounds gives

    2kδ²+3δ−2(k−3)/k≥0,
    5δ≥2(k−3)/k.

The positive root of the quadratic is (sqrt(16k−39)−3)/(4k). This proves (1) for every calibrated product and hence, by the non-increasing replacement, for every original physical product. For k=4 the quadratic becomes 16δ²+6δ−1≥0, whose positive root is exactly 1/8.

### 76.5 Attribution and boundary

The Gram spectral and dimension arguments use standard positive-matrix variational principles, closely related to the frame-rank inequalities behind Welch bounds; see [Datta, Howard and Cochran, Geometry of the Welch Bounds, §2](https://arxiv.org/abs/0909.0206). Stinespring representations, trace-distance tests and the diamond norm follow [Watrous, The Theory of Quantum Information, §§2.2 and 3.3](https://cs.uwaterloo.ca/~watrous/TQI/). Section 72 supplies the already established exact common-product calibration comparison. The new support-transfer estimate and the two-input argument provide the stated explicit obstruction for this uniform collapsed-fibre family.

The comparison is against one common physical product acting on every coherent input. Separate optimizers for the plus and minus tests are not allowed. Finite LOSR mixtures can implement the target exactly, so (1) is neither a lower bound for arbitrary shared randomness nor a linear separation from its convex feasible set. The result permits arbitrary local environments and physical leakage, and establishes bounds rather than an exact unrestricted optimum or a general RT recovery theorem.

## 77. The sharp rank-two Schmidt-support curve

### 77.1. Exact support envelope and its channel consequence

Let c₀ be a maximally entangled rank-two unit vector in arbitrary finite-dimensional bipartite spaces. Let P_A,P_B be its local Schmidt-support projections and

    Q=P_A⊗P_B−|c₀><c₀|.

This is a rank-three orthogonal projection. For any two local orthonormal pairs a_0,a_1 and b_0,b_1, define

    c=(a_0⊗b_0+a_1⊗b_1)/sqrt(2),
    d=(a_0⊗b_0−a_1⊗b_1)/sqrt(2),
    F=|<c₀,c>|²,  ℓ=||(I−Q)d||².

The dimension-independent sharp upper envelope, allowing arbitrary local dimensions, is

    ℓ_max(F)=min{1,2(1−sqrt(F))},  0≤F≤1.              (1)

Every value in (1) is attained using local dimension three. This sharp auxiliary statement strengthens §76's e+e² estimate, where e=1−F; it does not assert that a family of channel fibres can simultaneously attain every auxiliary equality.

For the uniform collapsed-fibre channel F_(k,2), k≥4, every original physical product of CPTP maps, with arbitrary environments and output leakage, consequently obeys

    ||(A⊗B)J_in−J_out F_(k,2)||diamond
       ≥2(k−3)/(3k).                                   (2)

The diamond norm is unhalved and the encodings are the fixed MC encodings of §§66 and 76, with full local input dimension 2k and output dimension k. At four fibres this gives 1/6. Together with §73 the unrestricted one-product optimum therefore lies in [1/6,1/3). Neither that channel optimum nor equality in (2) is claimed.

### 77.2. A two-dimensional contraction inequality

Write Z=diag(1,−1), and for a 2×2 matrix X let X₀=X−(TrX)I₂/2. For arbitrary complex contractions A,B of size two,

    |Tr(ABᵀ)|≤1+(1/2)||(AZBᵀ)₀||²_F.                 (3)

Here the transpose is the ordinary transpose, and the Frobenius norm is the Hilbert–Schmidt norm.

First prove that every 2×2 contraction R, with eigenvalues λ₁,λ₂, and every traceless Hermitian unitary N satisfy

    |Tr(NR)|≤1+|λ₁−λ₂|²/4.                            (4)

Put R into unitary Schur form [[λ₁,r],[0,λ₂]], transforming N by the same unitary similarity. In this basis N=[[a,b],[conj(b),−a]] with a real and a²+|b|²=1. Thus

    |Tr(NR)|=|a(λ₁−λ₂)+conj(b)r|
      ≤sqrt(|λ₁−λ₂|²+|r|²).

Positivity of I−R*R, specifically its determinant, gives

    |r|²≤(1−|λ₁|²)(1−|λ₂|²).                          (5)

For the scalar step set m=(λ₁+λ₂)/2, v=(λ₁−λ₂)/2, M=|m|², V=|v|² and h=Re(m conj(v)). Both eigenvalues have modulus at most one, hence M+V≤1. Direct expansion gives

    (1+V)²−[4V+(1−|λ₁|²)(1−|λ₂|²)]
       =M(2−2V−M)+4h²≥0.                              (6)

Indeed 2−2V−M≥0 follows from M+V≤1. Equations (5)–(6) prove (4), including repeated eigenvalues and singular contractions.

Now set R=ZBᵀA and T=AZBᵀ. Transposition preserves operator norm, so R is a contraction. The square matrices R and T have the same characteristic polynomial: their traces and determinants agree by cyclicity and multiplicativity. Also Tr(ZR)=Tr(ABᵀ). Applying (4) with N=Z gives

    |Tr(ABᵀ)|≤1+|λ₁−λ₂|²/4.

A Schur form of T has diagonal entries λ₁,λ₂, so

    ||T₀||²_F≥|λ₁−λ₂|²/2.

This proves (3). No simultaneous normality, invertibility, equality of A and conjugate(B), or common singular vectors is assumed.

### 77.3. Converting the contraction inequality to the sharp support bound

Choose local Schmidt bases of c₀ so that c₀=(|00>+|11>)/sqrt(2). Let A and B be the 2×2 matrices whose columns are the coordinates of P_A a_i and P_B b_i in these bases. Each is a compression of an isometry, hence is a contraction. Under the usual vectorization identification, the projections of c and d onto the anchor product support have coefficient matrices ABᵀ/sqrt(2) and AZBᵀ/sqrt(2). Therefore

    sqrt(F)=|Tr(ABᵀ)|/2,
    ||Qd||²=(1/2)||(AZBᵀ)₀||²_F.

Equation (3) gives 2sqrt(F)≤1+||Qd||², or ℓ≤2(1−sqrt(F)). Since d is a unit vector, also ℓ≤1. This proves the upper bound in (1).

For sharpness on F∈[1/4,1], use local dimension three with c₀=(|00>+|11>)/sqrt(2). For t∈[0,1] set

    v=sqrt(t)e_1+sqrt(1−t)e_2,
    a_0=b_0=(e_0+v)/sqrt(2),
    a_1=b_1=(e_0−v)/sqrt(2).

The local pairs are orthonormal. Direct expansion gives

    c=(|00>+v⊗v)/sqrt(2),
    d=(e_0⊗v+v⊗e_0)/sqrt(2),
    F=(1+t)²/4,  ||Qd||²=t,  ℓ=1−t=2(1−sqrt(F)).

For F∈[0,1/4], instead choose θ∈[0,π/4], v=cos(θ)e_0+i sin(θ)e_1, and

    a_0=b_0=(v+e_2)/sqrt(2),
    a_1=b_1=(v−e_2)/sqrt(2).

Now c=(v⊗v+|22>)/sqrt(2), d=(v⊗e_2+e_2⊗v)/sqrt(2), and

    F=cos²(2θ)/4,  Qd=0,  ℓ=1.

These two families cover the whole interval, agree at F=1/4, and prove exact attainment of (1), including F=0 and F=1.

### 77.4. An amplitude anchor yields the unrestricted channel bound

Use §72 to replace an arbitrary original product by a calibrated product with no greater error. No environment-dimension constraint is imposed, so possible enlargement of its environments is harmless. Let δ be the calibrated error; a lower bound for it is also a lower bound for the original error.

Write its actual joint records and their two coherent combinations as in §76:

    x_(f,i)=a_(f,i)⊗b_(f,i),
    c_f=(x_(f,0)+x_(f,1))/sqrt(2),
    d_f=(x_(f,0)−x_(f,1))/sqrt(2).

Each local pair is orthonormal. Let C and M be the Gram matrices of c_f and d_f, respectively. The normalized logical inputs

    |ψ_±>=k^(-1/2)Σ_f(|f,0>±|f,1>)/sqrt(2)

give actual logical outputs Cᵀ/k and Mᵀ/k, and ideal outputs J_k/k and I_k/k. The fixed MC output embedding preserves all norms. Thus, with c̄=k^(-1)Σ_f c_f,

    δ≥||C−J_k||₁/k≥2(1−||c̄||²),
    δ≥||M−I_k||₁/k.                                   (7)

The factor two in the first line follows by testing the trace-zero difference of two normalized states against the pure uniform state. These unreferenced coherent inputs are valid tests for the full-reference diamond norm.

The crucial anchor estimate uses amplitudes directly:

    (1/k)Σ_a Σ_f Re<c_a,c_f>
       =k||c̄||²≥k(1−δ/2).

Some actual fibre index a therefore satisfies

    Σ_f(1−|<c_a,c_f>|)
       ≤k−Σ_f Re<c_a,c_f>≤kδ/2.                        (8)

The anchor c_a has Schmidt rank two and equal Schmidt coefficients. Let Q be its rank-three support projection with the anchor direction removed. Apply (1) to each pair c_f,d_f. Using (8),

    Σ_f||(I−Q)d_f||²
       ≤2Σ_f(1−|<c_a,c_f>|)≤kδ.                        (9)

This step does not apply Jensen's inequality to the nonlinear curve, and does not treat the mean vector as a rank-two anchor.

Let B have columns d_f, so M=B*B. Since rank(QB)≤3, the sum of the k−3 smallest eigenvalues of M is at most Tr B*(I−Q)B≤kδ, by the variational argument in §76. If these eigenvalues are λ_1,...,λ_(k−3), the second normalized output test in (7), together with TrM=k, gives

    δ≥(2/k)Σ_j(1−λ_j)_+
      ≥(2/k)((k−3)−Σ_(j=1)^(k−3)λ_j)
      ≥2(k−3)/k−2δ.

Rearranging proves (2). The argument concerns the same physical product on both coherent inputs; optimizing them with different implementations would invalidate (8)–(9).

### 77.5. Attribution and scope

Unitary Schur decomposition is standard; see the [LAPACK Users’ Guide, Eigenvalues, Eigenvectors and Schur Factorization](https://www.netlib.org/lapack/lug/node50.html). Contraction positivity and Frobenius norms are standard matrix analysis; the channel normalization and Stinespring facts follow [Watrous, The Theory of Quantum Information, Chapters 1–3](https://cs.uwaterloo.ca/~watrous/TQI/). Sections 72 and 76 supply the existing calibration comparison and two-test spectral-deficit framework. The contraction calculation above proves the exact auxiliary support envelope, including explicit extremizers, and its amplitude-anchor application gives (2).

Sharpness in (1) is local to one anchor and one Schmidt sign-pair. It neither proves simultaneous compatibility of all fibre extremizers nor supplies a channel attaining (2). Finite LOSR mixtures can realize the target exactly, so (2) is specifically a one-product obstruction, with arbitrary local environments and original leakage. No general RT recovery theorem or literature priority for the underlying classical matrix tools is asserted.

## 78. A Schmidt-truncated common anchor for coherent fibre approximation

### 78.1. The high-purity centroid lemma

Let c_f be unit bipartite vectors with exactly two equal nonzero Schmidt coefficients, in arbitrary common finite-dimensional local spaces. Let p_f be nonnegative weights summing to one and let c_bar=sum_f p_f c_f. Suppose

    ||c_bar||^2 >= 1-epsilon/2,   0 <= epsilon < 1/2.

There is a unit vector c_star with exactly two equal Schmidt coefficients such that

    Re<c_star,c_bar> >= 1-u(epsilon)/2,
    u(epsilon)=(1-sqrt(1-2epsilon))/2.                 (1)

The bound is sharp as a statement about these centroids, already in local dimension three. The anchor is constructed from the two leading Schmidt directions of the centroid; the centroid itself is not asserted to have Schmidt rank two.

Proof. Identify vectors with coefficient matrices, preserving the Hilbert--Schmidt inner product, and set S=sqrt(2) Mat(c_bar). Every sqrt(2) Mat(c_f) has singular values 1,1,0,... . By convexity of the operator and nuclear norms,

    ||S||op <= 1,   ||S||_* <= 2,
    ||S||_F^2 >= 2-epsilon.                           (2)

Write its singular values as x_1>=x_2>=...>=0, and set L=x_1+x_2. For unequal local dimensions use a rectangular singular value decomposition, appending zero singular values as needed; both local dimensions are at least two. First

    sum_j x_j^2 <= x_1^2+x_2 sum_(j>=2) x_j
                  <= x_1^2+x_2(2-x_1) <= x_1+x_2=L.  (3)

The last difference is (1-x_1)(x_1-x_2)>=0. Hence L>=2-epsilon>3/2. Also L<=2. Put u=2-L, so 0<=u<1/2. The total tail mass is at most u, and therefore its squared mass is at most u^2. For fixed L, the convex function x^2+(L-x)^2 on L/2<=x<=1 is largest at x=1: the other endpoint differs by 2(1-L/2)^2. Consequently

    ||S||_F^2 <= 1+(L-1)^2+(2-L)^2
               =2-2u+2u^2.                          (4)

Combining (2) and (4) gives 2u(1-u)<=epsilon. Since u<1/2, inversion of this increasing function yields u<=u(epsilon). Choose a singular value decomposition S=sum_j x_j |a_j><b_j| and define Mat(c_star)=(|a_1><b_1|+|a_2><b_2|)/sqrt(2). Then c_star is a normalized equal-Schmidt rank-two vector and

    <c_star,c_bar>=L/2=1-u/2.

Repeated singular values cause no difficulty: choose any orthonormal singular vector pairs for the two leading values. This proves (1), with the usual conjugation of the right singular vectors when passing from coefficient matrices to bipartite vectors.

For sharpness choose orthonormal local basis vectors e_0,e_1,e_2, and take c_1=(|00>+|11>)/sqrt(2), c_2=(|00>+|22>)/sqrt(2) with weights 1-u,u, where 0<=u<1/2. Then S=diag(1,1-u,u), its squared norm is 2-2u+2u^2, and its maximal overlap with any normalized equal-Schmidt rank-two vector is (2-u)/2 by the variational characterization of the sum of the two largest singular values. Thus (1) is attained for epsilon=2u(1-u), covering [0,1/2). This sharpness does not assert that this two-vector family simultaneously saturates any channel approximation bound below.

### 78.2. The same anchor controls every Schmidt sign-pair

Suppose also that each c_f is presented through local orthonormal pairs as

    c_f=(a_(f,0) tensor b_(f,0)+a_(f,1) tensor b_(f,1))/sqrt(2),
    d_f=(a_(f,0) tensor b_(f,0)-a_(f,1) tensor b_(f,1))/sqrt(2).

Let Q_star be the rank-three projection onto the product of the two local Schmidt supports of c_star, with its own line removed. The sharp support inequality of section 77 applies to this constructed anchor and every actual pair c_f,d_f. Thus

    sum_f p_f ||(I-Q_star)d_f||^2
       <=2 sum_f p_f(1-|<c_star,c_f>|)
       <=2(1-Re<c_star,c_bar>) <=u(epsilon).          (5)

Only the anchor is newly chosen. The vectors d_f remain the original joint records, with their mutual Gram matrix and all phases unchanged. No independent choice of equality frames is made.

### 78.3. An unrestricted channel consequence

For the uniform collapsed-fibre channel F_(k,2), with the fixed MC input and output encodings of sections 66 and 72, write delta for the unhalved diamond error of one common physical product of CPTP maps. Arbitrary original output leakage and arbitrary finite local environments are permitted. For integers 4<=k<=12,

    delta >= (sqrt(12k)-6)/k.                         (6)

For k=4 this is sqrt(3)-3/2, approximately 0.23205. Together with the strict upper construction in section 73, the unrestricted four-fibre optimum lies in [sqrt(3)-3/2,1/3). Equality in (6), and the exact channel optimum, are not asserted. For k>12 the existing section 77 bound 2(k-3)/(3k) is stronger than the threshold 1/2 supplied by this high-purity argument.

Proof. Apply section 72's calibration comparison to the original product. It suffices to lower-bound the error delta of the resulting calibrated product, since that error does not exceed the original error. No environment-dimension resource constraint is imposed here. Its actual records determine c_f,d_f as above. The two normalized coherent inputs

    |psi_+->=k^(-1/2) sum_f (|f,0> +/- |f,1>)/sqrt(2)

give logical outputs C^T/k and M^T/k, where C and M are the Gram matrices of c_f and d_f. Their ideal outputs are J_k/k and I_k/k. As in section 77, trace-zero normalization gives

    ||k^(-1) sum_f c_f||^2 >=1-delta/2,
    delta >= ||M-I_k||_1/k.                          (7)

These normalized state tests lower-bound the full arbitrary-reference diamond norm; the output MC embedding preserves trace norms.

If delta>=1/2, (6) already follows, because (sqrt(12k)-6)/k<=1/2 for 4<=k<=12, equivalently (sqrt(k)-sqrt(12))^2>=0. Otherwise apply (5) with p_f=1/k and epsilon=delta. For B with columns d_f,

    Tr B*(I-Q_star)B <= k u(delta),   rank(Q_star B)<=3.

The variational principle bounds the sum of the k-3 smallest eigenvalues of M=B*B by k u(delta). Since Tr M=k, the second test in (7) yields

    delta >= 2(k-3)/k-2u(delta)
           =1-6/k+sqrt(1-2delta).                    (8)

In particular delta-1+6/k is nonnegative. Squaring the inequality sqrt(1-2delta)<=delta-1+6/k is therefore legitimate and gives

    delta^2+(12/k)delta+36/k^2-12/k >=0.

Its nonnegative root is (sqrt(12k)-6)/k. This proves (6). At k=12, (8) rules out delta<1/2; for k>12 it does so as well. The proof uses one common physical channel and one common Schmidt-truncated anchor for all fibres. It does not replace either party's local records or assume simultaneous attainment of the auxiliary inequalities.

### 78.4. Attribution and scope

Singular value decomposition, the operator/nuclear norm triangle inequalities, and the variational characterization of the sum of the two largest singular values are standard matrix-analysis ingredients; see [Watrous, The Theory of Quantum Information, Chapter 1](https://cs.uwaterloo.ca/~watrous/TQI/TQI.1.pdf) for singular values, Schatten norms, and their variational formulations. No priority claim is made for these ingredients. The original-channel calibration and trace-norm tests are the results of sections 72 and 77. The centroid lemma proves the particular sharp high-purity tradeoff (1), and (5) transports its constructed anchor to all original Schmidt sign-pairs simultaneously. This is a paper theorem concerning the fixed uniform fibre family. The channel lower bound is not an exact optimum, does not restrict the environment dimension, and does not apply to arbitrary finite LOSR mixtures, which can realize the target exactly.

## 79. An exact tetrahedral marker family with quarter-error product realization

### 79.1. Physical family and its exact diamond error

Let F_(4,2) be the uniform four-fibre target of sections 66 and 72, with fixed MC encodings. Let the four tetrahedral Bloch vectors be

    n_1=(1,1,1)/sqrt(3), n_2=(1,-1,-1)/sqrt(3),
    n_3=(-1,1,-1)/sqrt(3), n_4=(-1,-1,1)/sqrt(3).

For each f choose an orthonormal qubit basis u_(f,0),u_(f,1) whose projectors are (I+(-1)^j n_f dot sigma)/2. For a complex parameter eta with |eta|<=1, choose unit marker vectors a_0,a_1 satisfying <a_1,a_0>=eta; for example

    a_0=e_0, a_1=conj(eta)e_0+sqrt(1-|eta|^2)e_1.

Define local Stinespring isometries on the full eight-dimensional local inputs by

    V_A|f,j>=|f> tensor u_(f,j) tensor a_j,
    V_B|f,j>=|f> tensor conj(u_(f,j)).                  (1)

Tracing the environments gives one physical product channel, denoted A_eta tensor B. It acts on every coherent input with the same maps. Its exact unhalved, arbitrary-reference diamond error is

    ||(A_eta tensor B) J_in-J_out F_(4,2)||diamond
       =1/4+|eta-3/4|.                                (2)

In particular eta=3/4 gives an exact error of 1/4. This is the unique optimal parameter within this marker family. The original unrestricted product optimum is not determined: together with section 78 it lies in

    [sqrt(3)-3/2, 1/4].                               (3)

At eta=3/4 the local channels in (1) have Kraus ranks exactly four and two, respectively. This is an attaining resource count for (2), not a minimal-resource claim for quarter error.

### 79.2. All coherent matrix units and the marker mechanism

The vectors on the right of (1) are orthonormal over all input labels: different f have orthogonal output labels, and within a fibre the u_(f,j) are orthogonal. Thus both maps are isometries, including when marker vectors coincide. For f!=g the tetrahedral identity n_f dot n_g=-1/3 gives

    |<u_(f,i),u_(g,j)>|^2
       =(1+(-1)^(i+j) n_f dot n_g)/2
       =1/3 if i=j, and 2/3 if i!=j.                 (4)

The conjugate qubit records on the other party cancel the phases of these overlaps. With the convention that the output coefficient for |f,i><g,j| is the environment inner product in the order (g,j),(f,i), the retained coefficients are therefore

    C_(f0,g0)=C_(f1,g1)=1/3,
    C_(f0,g1)=2eta/3, C_(f1,g0)=2conj(eta)/3          (f!=g).

For f=g the coefficient is delta_ij. The target has the same diagonal blocks I_2 and every off-diagonal block J_2/2. Consequently the difference kernel is

    D=(J_4-I_4) tensor R_eta,
    R_eta=[[-1/6, 2eta/3-1/2],
           [2conj(eta)/3-1/2, -1/6]].                (5)

This verifies every matrix unit, not only a selected input state. At eta=3/4 the unequal-bit coefficients match the target exactly, leaving R_eta=-I_2/6.

### 79.3. Full-reference norm and an attaining input

Write Q_4=id-Delta_4, where Delta_4 is complete dephasing in the fibre basis. On the logical input C^4 tensor C^2 define the Hermitian scalar functional

    phi_R(X)=Tr(R^T X).

By (5), the logical channel difference, before the fixed output MC isometry, is exactly

    Q_4 composed with (id_4 tensor phi_(R_eta)).       (6)

The transpose in this functional is necessary: Tr(R^T |i><j|)=R_ij. The eigenvalues of the Hermitian matrix R_eta are

    -1/6 +/- |2eta/3-1/2|.

For any Hermitian two-dimensional matrix R, (6) has diamond norm

    ||Q_4||diamond ||R||op.                           (7)

To prove the upper bound with arbitrary references, diagonalize R^T=sum_s beta_s Pi_s. On a normalized positive input with any reference, the two partial traces obtained by the orthogonal projections Pi_s are positive operators with traces summing to one. Applying Q_4 to each, using its diamond norm, and applying the triangle inequality bounds the output trace norm by ||Q_4||diamond max_s|beta_s|. A Hermiticity-preserving map's diamond norm can be optimized on normalized positive inputs with a reference, so this proves the upper bound. Conversely choose a bit eigenstate of R^T with eigenvalue of maximal absolute value and an input attaining the norm of Q_4. This proves (7).

For completeness ||Q_4||diamond=3/2. Let Z=diag(1,i,-1,-i). The identity Delta_4=(1/4)sum_(a=0)^3 Ad_(Z^a) gives

    Q_4=(3/4)id-(1/4)sum_(a=1)^3 Ad_(Z^a),

so the triangle inequality gives the upper bound 3/2. On the normalized uniform vector |s>=(1/2)sum_f |f>, Q_4(|s><s|) has eigenvalues 3/4,-1/4,-1/4,-1/4, attaining 3/2 without any reference. Therefore

    ||Q_4||diamond ||R_eta||op
       =(3/2)(1/6+|2eta/3-1/2|)=1/4+|eta-3/4|.

The fixed output MC isometry preserves these norms and proves (2). At eta=3/4 any normalized bit state tensored with |s> attains the value 1/4. The physical input is its fixed MC encoding. All arbitrary-reference inputs obey the matching upper bound.

### 79.4. Exact local ranks and scope

When |eta|<1, the markers a_0,a_1 are linearly independent. For each fixed j, the four qubit vectors u_(f,j) span C^2: their projectors have distinct Bloch vectors and are not a common line. Hence the A-environment records span

    C^2 tensor span{a_0,a_1}=C^4,

while the B-environment records span C^2. In a calibrated Stinespring map (1), the Kraus operators indexed by an environment basis are linearly independent precisely when those records span the environment: a linear combination of the Kraus operators vanishes if and only if its environment covector annihilates every record. Thus the local Kraus ranks are exactly (4,2), in particular at eta=3/4. The construction uses no shared randomness or communication.

The tetrahedral Bloch identity is the same standard qubit geometry used in sections 70 and 73; the marker is an ordinary Stinespring environment record. The norm facts and the Hermiticity-preserving diamond formulation are standard; see [Watrous, The Theory of Quantum Information, section 3.3](https://cs.uwaterloo.ca/~watrous/TQI/). The explicit calculation above optimizes this entire complex marker family and gives a common physical implementation attaining 1/4. It supplies an upper bound for the unrestricted problem, not a proof that all original leakage-bearing product channels have error at least 1/4. Sections 72 and 78 retain their stated unrestricted scope.

## 80. A Pauli-kernel obstruction for a calibrated qubit environment

### 80.1. Statement and exact four-fibre consequence

Let k >= 2. For every f=1,...,k, let (a_f0,a_f1) be an orthonormal pair in an arbitrary common finite-dimensional complex Hilbert space A, and let (b_f0,b_f1) be an orthonormal basis of a common two-dimensional Hilbert space B. Define

    x_fi = a_fi tensor b_fi,
    K_(fi,gj) = <x_fi,x_gj>.

Let T have diagonal 2-by-2 blocks I_2 and every off-diagonal block J_2/2. There is an explicit product-dependent orthogonal projection P such that

    Tr P(K-T) <= -r,
    ||K-T||_1 >= 2r,
    r = k - dim_R span{N_1,...,N_k} >= k-3,             (1)

where N_f are the traceless Hermitian qubit involutions defined below. In particular, for k=4,

    ||K-T||_1 >= 2.                                    (2)

This holds with arbitrary complex, nonconjugate A records and no bound on their dimension. The only resource restriction is that the B records all lie in one common two-dimensional space. The parties can be interchanged.

For the calibrated physical product channels determined by these records, the unhalved arbitrary-reference diamond error satisfies

    delta >= r/k >= (k-3)/k  (k>=4).                    (3)

At k=4 the minimum over this entire calibrated class is exactly 1/4: the tetrahedral-marker construction of section 79 attains 1/4 with local environment dimensions (4,2). Thus (2) supplies a matching lower bound for every calibrated (arbitrary,2) product, not only conjugate-paired or fibre-independent marker competitors. It does not determine the unrestricted two-sided environment optimum.

A physical scope extension is valid: the party with Kraus rank two must be exactly fibre-calibrated, but the other party may initially have arbitrary output leakage. Calibrating only the other party does not increase the error and leaves the rank-two party unchanged. Section 80.5 gives this comparison. No claim is made here for an arbitrary uncalibrated rank-two party.

### 80.2. Coefficient matrices and the common Pauli space

Choose orthonormal bases in A and B, and identify a bipartite vector with its coefficient matrix, isometrically for the Hilbert--Schmidt inner product. Let A_f and B_f be the matrices whose columns are a_f0,a_f1 and b_f0,b_f1, respectively. Thus A_f^* A_f=I_2 and B_f is a 2-by-2 unitary matrix. With Z=diag(1,-1), put

    C_f = A_f B_f^T / sqrt(2),
    D_f = A_f Z B_f^T / sqrt(2),
    N_f = conjugate(B_f) Z B_f^T.                       (4)

These are the coefficient matrices of

    c_f = (x_f0+x_f1)/sqrt(2),
    d_f = (x_f0-x_f1)/sqrt(2).

Since B_f^T conjugate(B_f)=I_2,

    D_f = C_f N_f.                                     (5)

Moreover N_f is Hermitian, has trace zero, and N_f^2=I_2. It lies in the real three-dimensional space of traceless Hermitian 2-by-2 matrices. Let

    L = {v in R^k : sum_f v_f N_f = 0},
    r = dim_R L = k-dim_R span{N_f}.

Choose a real k-by-r matrix V whose columns form an orthonormal basis of L. Its complexification is an isometric inclusion C^r -> C^k, and Pi=VV^T is an orthogonal projection on C^k. All identities below remain valid for complex linear combinations of its columns.

### 80.3. A variance bound restricted to the actual Pauli kernel

Put

    S = (1/k) sum_f C_f,
    E_f = C_f-S,
    a = sum_f ||E_f||_F^2 = k-k||S||_F^2.              (6)

The final equality uses ||C_f||_F=1. Define a linear map Zeta:C^k -> A tensor B by giving its f-th column the coefficient matrix E_f N_f. Since N_f is unitary,

    ||Zeta||_F^2 = sum_f ||E_f N_f||_F^2 = a.           (7)

Let D:C^k -> A tensor B have columns d_f. For every v in the complexification of L, (5) gives

    Mat(Dv) = sum_f v_f C_f N_f
            = sum_f v_f E_f N_f + S sum_f v_f N_f
            = Mat(Zeta v).

Consequently DV=Zeta V. If M=D^*D is the Gram matrix of the original d_f, then

    Tr(Pi M) = ||DV||_F^2 = ||Zeta V||_F^2
             = Tr(Pi Zeta^*Zeta) <= Tr(Zeta^*Zeta)=a.  (8)

The projection contraction in (8) is essential: the bound is a, not r times a. No d_f is replaced, no equality frame is independently chosen, and their mutual Gram matrix and phases are unchanged.

This is a restricted-environment statement. The three-dimensional nullity bound does not extend to arbitrary B environments: the matrices then need not lie in one common three-dimensional Pauli space.

### 80.4. An explicit full-matrix dual witness

Apply the orthogonal plus/minus change of basis on each input fibre and then order all plus coordinates before all minus coordinates. The complete transformed matrices are

    Khat = [ C   X ],       That = [ J_k  0 ],
           [ X^* M ]               [ 0   I_k ],

where C is the Gram matrix of c_f and X is their actual cross-Gram block with d_f. X is not assumed to vanish or deleted from the matrix under study.

Let s=(1,...,1)^T/sqrt(k) and define the orthogonal projection

    Phat = diag(ss^*, Pi).

Its rank is r+1. The plus Rayleigh value is

    s^*(C-J_k)s = k||S||_F^2-k = -a.

Equation (8) gives the minus-block trace at most a-r. Hence

    Tr Phat(Khat-That) <= -a+(a-r) = -r.               (9)

Conjugating Phat back yields P in (1). Since Tr(K-T)=0, W=I-2P is a Hermitian contraction with

    Tr W(K-T) = -2 Tr P(K-T) >= 2r.

Trace-norm duality proves (1). Equivalently, the sum of the r+1 smallest eigenvalues of K-T is at most -r. For four generic Pauli directions r=1, the two smallest eigenvalues sum to at most -1. The witness remains valid in the presence of every plus/minus cross coupling, because it is a legitimate test against the full matrix.

For the associated calibrated channels, the actual retained output coefficient is the transpose of the forward Gram K used here: for the normalized maximally entangled logical/reference input, the physical output difference has matrix (K-T)^T/(2k) on the orthonormal support {|f,i>_reference tensor |ff>_output}. Transposition preserves trace norm. Equivalently, the uniform logical density rho=I_(2k)/(2k) is allowed in the exact full-reference norm formula. Therefore

    delta >= ||K-T||_1/(2k) >= r/k,

which proves (3). At k=4, section 79's eta=3/4 tetrahedral marker has full diamond error 1/4, so the lower bound is attained in this class.

### 80.5. Allowing leakage on the other party only

Suppose B:C^(2k)->C^k is exactly fibre-calibrated and has Kraus rank two, while A is an arbitrary CPTP map. B admits records as in section 80.1, is covariant under the input/output fibre phases of section 72, and remains unchanged under that phase action. Independently averaging only A over those phases therefore cannot increase the product's error from the covariant target.

The twirled A has the section-72 zero-charge block Q>=0 and wrong-output blocks P_(a,f)>=0, with Q_ff+sum_(a!=f)P_(a,f)=I_2. Replace Q by Q'=Q+directsum_f(I_2-Q_ff), and delete the wrong-output blocks. This repairs A only; B and its two-dimensional environment are unchanged.

The same reference-tag comparison as section 72 now has correct-output coefficient block Q_ff entrywise-multiplied by I_2, namely diag(Q_ff), which is bounded above by I_2. Thus the missing correct-output population D is positive. Every wrong A output is orthogonal to the correct output/tag sector because B's output is already f. The wrong-output population X is positive and has Tr X=Tr D. All cross-fibre coefficients are unchanged. On every normalized tagged reference input the original twirled error is C-D+X, whereas the repaired error is C, with C,D supported on the correct sector and X on its orthogonal complement. Hence

    ||C||_1 <= ||C-D||_1+Tr D
             = ||C-D||_1+Tr X = ||C-D+X||_1.

Taking the arbitrary-reference supremum shows that repairing A cannot increase the diamond error. The repaired pair obeys (3), so the same lower bound applies to the original A with leakage. In particular, the exact four-fibre infimum is 1/4 when B is fibre-calibrated of Kraus rank two and A is any CPTP map, with the symmetric statement obtained by exchanging parties.

This argument does not calibrate an arbitrary rank-two B while preserving its rank. The unrestricted calibration theorem can increase local Kraus ranks, so no such implication is used or claimed.

### 80.6. Fixed-marker subclass

For any four qubit bases u_fj, let n_f be their Bloch axes, let the other party use conjugate(u_fj), and attach arbitrary fixed bit markers m_0,m_1 with forward overlap eta=<m_0,m_1>, |eta|<=1. This eta is the complex conjugate of section 79's reverse-overlap parameter; their real optimizing value 3/4 agrees. Set

    R_fg=n_f dot n_g,
    A_eta=[[1,eta],[conjugate(eta),1]],
    B_eta=[[1,-eta],[-conjugate(eta),1]].

Then K=(J_4 tensor A_eta+R tensor B_eta)/2, while

    T=(J_4 tensor J_2)/2+I_4 tensor(I_2-J_2/2).

For any unit v in ker R, the rank-two projection P_v=|v><v| tensor I_2 satisfies Tr P_v(K-T)=-1 exactly. This is a simpler special-case dual witness; it requires neither tetrahedral geometry nor real eta. The broader Pauli-kernel theorem above does not require this marker structure at all.

### 80.7. A fixed-dimensional calibrated environment resource law

Let the qubit-fibre target T have diagonal blocks I_2 and off-diagonal blocks J_2/2. Let a_f0,a_f1 be orthonormal pairs in an arbitrary A environment, and let b_f0,b_f1 be orthonormal pairs in one common B environment of dimension d>=2. The local B channel is exactly fibre-calibrated; the A channel can initially have arbitrary output leakage, since the one-sided comparison in section 80.5 calibrates A without modifying B.

With A_f and B_f the matrices of these frames, B_f is now d-by-2 and B_f^*B_f=I_2. Define

    C_f=A_f B_f^T/sqrt(2),
    D_f=A_f Z B_f^T/sqrt(2),
    N_f=conjugate(B_f) Z B_f^T,   Z=diag(1,-1).

Then D_f=C_fN_f because B_f^T conjugate(B_f)=I_2. Every N_f is a d-by-d traceless Hermitian matrix, with eigenvalues 1,-1 and d-2 zeros; in particular ||N_f||op=1. Put

    m=dim_R span{N_1,...,N_k} <= d^2-1,
    r=k-m.

Choose a real k-by-r isometry V spanning the kernel of v -> sum_f v_fN_f and set Pi=VV^T. Let S=k^(-1)sum_f C_f, E_f=C_f-S, and a=sum_f||E_f||_F^2=k-k||S||_F^2. Let D have columns Mat^(-1)(D_f), and let Zeta have columns Mat^(-1)(E_fN_f). The kernel identity gives DV=Zeta V, while the contraction property gives

    ||Zeta||_F^2=sum_f||E_fN_f||_F^2
               <=sum_f||E_f||_F^2=a.

Therefore Tr(Pi D^*D)=||DV||_F^2<=a. In the complete plus/minus representation Khat=[[C,X],[X^*,M]], with C and M the original plus/minus Grams and X their original cross block, choose the projection Phat=diag(ss^*,Pi), s=ones/sqrt(k). Its plus expectation is -a for Khat-That and its minus trace is at most a-r. Thus Tr Phat(Khat-That)<=-r. Since Tr(K-T)=0,

    ||K-T||_1 >=2r,
    delta >= ||K-T||_1/(2k) >=r/k
          >=max{0, (k-d^2+1)/k}.                       (10)

The diamond inequality uses the normalized maximally entangled logical/reference input. Its physical error is represented by (K-T)^T/(2k) on the orthonormal support {|f,i>_reference tensor |ff>_output}, and transposition preserves trace norm.

Consequently a necessary local environment resource condition is

    d^2 >= k(1-delta)+1.                               (11)

This is a necessary condition, not a sufficiency or minimal-environment theorem. It applies when the dimension-d party is exactly fibre-calibrated, with arbitrary original leakage permitted only on the other party by the one-sided repair. An arbitrary uncalibrated dimension-d party is not covered. At d=2 the result specializes to section 80's qubit theorem and its exact four-fibre value 1/4. The unrestricted four-fibre optimum with both local environments arbitrary remains open.


### 80.8. Attribution and boundary

The proof uses the standard Pauli-space dimension, Hilbert--Schmidt projection contraction, and trace-norm duality; see [Watrous, The Theory of Quantum Information, Chapters 1 and 3](https://cs.uwaterloo.ca/~watrous/TQI/) for matrix-norm and channel-norm background. The full-reference Gram norm and one-sided reference-tag comparison use the framework proved in section 72. The attaining physical product and exact arbitrary-reference norm are section 79's tetrahedral-marker theorem. No external numerical optimizer or numerical nonfinding is used as evidence for (1)--(3). The unrestricted four-fibre optimum with both environments arbitrary remains open between sqrt(3)-3/2 and 1/4.

## 81. A subnormalized centroid-support witness for original local environment bounds

### 81.1. Original-channel theorem, including output leakage

Let k>=2 be an integer and let F_(k,2):C^(2k)->C^k be the uniform qubit-fibre target,

    F(|f,i><f,j|)=delta_ij |f><f|,
    F(|f,i><g,j|)=(1/2)|f><g| for f!=g.

Fix the MC input and output encodings J_in and J_out. Let A,B:C^(2k)->C^k be arbitrary CPTP maps. If B admits a pure Stinespring environment of dimension d (equivalently, has Kraus rank at most d), then their unhalved, arbitrary-reference diamond error obeys

    delta=||(A tensor B)J_in-J_out F_(k,2)||diamond
         >= max{0,(k-d^2+1)/k}.                         (1)

Necessarily d>=2: B's Stinespring isometry maps an input of dimension 2k into an output-environment space of dimension kd, so 2k<=kd. The environment dimension and output leakage of A are unrestricted. B need not be fibre-calibrated, either. The same bound holds with the parties exchanged. Consequently an actual local Kraus rank d must satisfy

    d^2 >= k(1-delta)+1.                                (2)

At k=4, the exact minimum over all original physical products with either local Kraus rank at most two is 1/4. The lower bound follows from (1), and the eta=3/4 tetrahedral-marker product of section 79 attains it with local Kraus ranks (4,2). This permits arbitrary nonconjugate local maps and arbitrary output leakage on both sides. Any product with error strictly below 1/4 must therefore have both local Kraus ranks at least three. It remains open whether such a product exists: the unrestricted four-fibre optimum is still only known to lie in [sqrt(3)-3/2,1/4].

The proof below is direct on the original Stinespring records and a normalized reference input. It uses neither calibration nor an error-monotonicity assertion for unitary polar replacement.

### 81.2. A pointwise centroid-support inequality for contractions

Let A_0:C^2->E be a contraction, let H:C^2->C^d be a contraction, and let Z=diag(1,-1). Identify E tensor C^d with coefficient matrices E-by-d, preserving the Hilbert--Schmidt inner product. Set

    C=A_0 H^T/sqrt(2),
    D=A_0 Z H^T/sqrt(2).

For any fixed matrix S of the same size, define the complex linear subspace

    L_S={S X : X is d-by-d and Tr X=0},

and let Q_S be its Hilbert--Schmidt orthogonal projection. Its dimension is at most d^2-1. Then

    ||(I-Q_S)D||_F^2
       <= 1+||S||_F^2-2 Re Tr(S^* C).                  (3)

The assertion is universal in S. S is not assumed normalized, maximally entangled, or of a prescribed rank.

First suppose H=U is an isometry, U^*U=I_2. Define

    N=conjugate(U) Z U^T.

Since U^T conjugate(U)=I_2, one has D=C N. The matrix N is Hermitian and traceless, and ||N||op=1; its nonzero eigenvalues are 1 and -1. Thus S N belongs to L_S. Orthogonal projection and multiplication by a contraction give

    ||(I-Q_S)D||_F^2
       <= ||D-S N||_F^2
        = ||(C-S)N||_F^2
       <= ||C-S||_F^2
       <= 1+||S||_F^2-2 Re Tr(S^* C).                  (4)

The last inequality uses ||C||_F^2=Tr(A_0^*A_0)/2<=1.

For a general contraction H, take a thin singular value decomposition

    H=L diag(s_1,s_2)V^*,  0<=s_1,s_2<=1,
    L^*L=I_2,  V^*V=I_2.

Zero singular vectors can be completed to an orthonormal pair because d>=2. For epsilon=(epsilon_1,epsilon_2) in {+1,-1}^2 set

    U_epsilon=L diag(epsilon_1,epsilon_2)V^*,
    p_epsilon=((1+epsilon_1 s_1)(1+epsilon_2 s_2))/4.

Every U_epsilon is an isometry, the p_epsilon are nonnegative and sum to one, and H=sum_epsilon p_epsilon U_epsilon. Both C and D depend linearly on H. For fixed A_0 and S, the function

    H -> ||(I-Q_S)D||_F^2+2 Re Tr(S^* C)

is convex: its first term is a squared norm of a linear map and its second term is real-linear. Averaging (4) over this explicit isometric decomposition proves (3). This convexity step is applied to the support-loss expression, not to a claim that polar normalization decreases channel error.

### 81.3. The full subnormalized Gram witness

For f=1,...,k, let A_f:C^2->E_A and H_f:C^2->C^d be contractions. Their columns are a_fi and h_fi. Define the actual product records and their forward Gram by

    x_fi=a_fi tensor h_fi,
    K_(fi,gj)=<x_fi,x_gj>.

Let T have diagonal blocks I_2 and off-diagonal blocks J_2/2. Define

    c_f=(x_f0+x_f1)/sqrt(2),
    d_f=(x_f0-x_f1)/sqrt(2),
    C_f=Mat(c_f)=A_f H_f^T/sqrt(2),
    D_f=Mat(d_f)=A_f Z H_f^T/sqrt(2),
    S=(1/k)sum_f C_f,
    a=k-k||S||_F^2.

Apply (3) to every fibre with this one common S and Q=Q_S. Summing gives

    sum_f ||(I-Q)D_f||_F^2 <= a.                       (5)

Let B:C^k->E_A tensor C^d have columns d_f. Choose an isometry V whose range is ker(QB), and put

    r=dim ker(QB),   Pi=VV^*.

In particular r>=max{0,k-d^2+1}. The identity QBV=0 and Hilbert--Schmidt projection contraction imply

    Tr(Pi B^*B)=||BV||_F^2
               =||(I-Q)BV||_F^2
              <=||(I-Q)B||_F^2 <=a.                  (6)

Apply the plus/minus change of basis to K and T, and order all plus coordinates before all minus coordinates. The complete transformed matrices are

    Khat=[[Cgram,X],[X^*,M]],
    That=diag(J_k,I_k),

where M=B^*B and X is the actual plus/minus cross block. No cross coupling is discarded. With s=ones/sqrt(k),

    s^*(Cgram-J_k)s=k||S||_F^2-k=-a.

The orthogonal projection Phat=diag(ss^*,Pi) therefore satisfies

    Tr Phat(Khat-That) <= -a+(a-r)=-r.                 (7)

Conjugating back gives an explicit projection P on the full original coefficient space. The positive-part variational principle yields

    Tr(T-K)_+ >= Tr P(T-K) >= r
               >=max{0,k-d^2+1}.                     (8)

This argument does not assume TrK=2k. Equivalently,

    ||K-T||_1+2k-TrK >=2r.                            (9)

Thus it retains the full loss deficit of subnormalized correct-output records. It proves the desired four-fibre independent-contraction lemma Tr(T-K)_+>=1 whenever d=2, even without requiring the A_f to be orthonormal frames.

### 81.4. Direct application to the original physical channel

Choose Stinespring isometries V_A,V_B of the original local maps, with B environment dimension d. For each f let A_f and H_f be their correct-output blocks:

    A_f e_i=(<f|_out tensor I_EA)V_A|f,i>,
    H_f e_i=(<f|_out tensor I_EB)V_B|f,i>.

Projection of an isometry is a contraction, so A_f^*A_f<=I_2 and H_f^*H_f<=I_2. Their records determine exactly the K of section 81.3. The original B isometry is square when d=2, but that additional block-unitary compatibility is not needed: (8) holds for all independent contraction blocks.

Use the normalized maximally entangled logical/reference input

    |Omega>=(1/sqrt(2k))sum_(f,i) |f,i>_R tensor |f,i>_logical.

Let sigma be the original product-channel output after the input MC encoding, and let tau be the target output. Let W send |f,i> to |f,i>_R tensor |ff>_out and set P_good=WW^*. Directly from the Stinespring inner products,

    P_good sigma P_good = W K^T W^*/(2k),
    tau = W T W^*/(2k).

The transpose is because K is the forward Gram; T is real symmetric. Pinching into the good subspace and its orthogonal complement is trace-norm contractive on Hermitian operators. The target vanishes on the complementary subspace, and the corresponding actual block is positive. Since sigma has trace one,

    ||sigma-tau||_1
       >= ||K-T||_1/(2k) + 1-TrK/(2k)
        = Tr(T-K)_+/k
       >= max{0,(k-d^2+1)/k}.                         (10)

All off-diagonal coherences between these two support sectors were handled by a valid CPTP pinching lower bound; none is assumed absent. The retained matrix K includes every within-fibre and cross-fibre coherence in the good sector. The diamond norm is at least the error on this one normalized reference input, so (10) proves (1) for the original maps, including arbitrary leakage and every reference permitted in the definition.

### 81.5. Attribution, resource interpretation, and boundary

The proof uses standard singular value decomposition, an explicit convex decomposition of a rectangular contraction into isometries, Hilbert--Schmidt projection contraction, the positive-part variational principle, and trace-norm contractivity of pinching; see [Watrous, The Theory of Quantum Information, Chapters 1--3](https://cs.uwaterloo.ca/~watrous/TQI/) for the matrix and channel background. The new pointwise inequality (3) transfers a common centroid-support witness through the contraction decomposition and, crucially, retains the missing Choi trace in (9)--(10). Section 79 supplies the attaining physical product and its exact arbitrary-reference error. The normalized Choi and Stinespring conventions agree with sections 72 and 74, but no calibration theorem is used here.

The resource d is the dimension of a pure Stinespring environment, or local Kraus rank. A mixed ancilla's purification must be included. Equation (2) is a necessary bound, not a sufficiency statement for arbitrary k,d. At k=4,d=2 the exact value 1/4 is established by the matching construction. The general arbitrary-rank four-fibre optimum remains unresolved; this result does not prove ||G entrywise-multiplied by H-T||_1>=2 when both Gram factors have unrestricted rank.

## 82. Quarter-error rigidity, minimal Kraus product, and the complete rank-two-party family

### 82.1. Original-channel theorem and equality classification

Let F=F_(4,2) be the logical channel from C^4 tensor C^2 to C^4 defined by

    F(|f,i><f,j|)=delta_ij |f><f|,
    F(|f,i><g,j|)=(1/2)|f><g|  for f!=g.

All diamond norms are unhalved and permit arbitrary references. Use the fixed input and output maximally-correlated encodings J_in and J_out. Let A,B:C^8->C^4 be original CPTP maps, and put

    delta=||(A tensor B)J_in-J_out F||diamond.

**Theorem.** If B has Kraus rank two and delta=1/4, then both original channels are exactly fibre-calibrated: every input |f,i> has output support in |f>. Moreover A has Kraus rank exactly four. The statement is symmetric in A and B.

Consequently the minimum product of local Kraus ranks among all original physical products having error exactly 1/4 is eight. In particular no rank pair (2,2), (2,3), or (3,2) attains quarter error. The known eta=3/4 tetrahedral-marker product has ranks (4,2) and attains the minimum. This does not settle whether products with both ranks at least three can have error below 1/4.

The equality family is also complete within this rank-two-party class. After exchanging the parties if needed, environment isometries and independent simultaneous input-bit swaps in the two local channels put every equality product into a fixed-marker form with overlap 3/4. Its four balanced Bloch axes have a disphenoid Gram, parametrized by x^2+y^2+z^2=1, and exact quarter error is equivalent to x^2,y^2,z^2>=2/7. Sections 82.9--82.12 prove necessity and sufficiency, including the full-reference upper bound. These equivalences use only the stated target-preserving swaps, not arbitrary changes of the input bit bases.

A pure Stinespring environment dimension is meant throughout, and a mixed environment must be purified. Each local Kraus rank is at least two, since a Stinespring isometry C^8->C^4 tensor C^d requires 8<=4d.

### 82.2. Correct-output contractions and an equality-sensitive support witness

Choose Stinespring isometries for the original maps, taking the B environment to be C^2. For each fibre their correct-output blocks are contractions

    A_f:C^2->E_A,   H_f:C^2->C^2,
    A_f e_i=(<f| tensor I)V_A|f,i>,
    H_f e_i=(<f| tensor I)V_B|f,i>.

Define coefficient matrices, using the standard Hilbert--Schmidt inner product <Y,Z>=Tr(Y^*Z),

    C_f=A_f H_f^T/sqrt(2),
    D_f=A_f Z H_f^T/sqrt(2),   Z=diag(1,-1),
    S=(1/4)sum_f C_f,   p=||S||_F^2,   a=4-4p,
    t_f=Tr(A_f^* A_f)/2,   epsilon_A=sum_f(1-t_f).

Coefficient matrices identify E_A tensor C^2 isometrically with its tensor-product vectors. Let

    L_S={S X: X is 2-by-2 and Tr X=0},
    Q=orthogonal projection onto L_S.

For the actual product records x_fi=a_fi tensor h_fi, write their forward Gram as K. After changing each bit basis to |+>,|-> and ordering all plus coordinates first,

    Khat=[[Cgram,X],[X^*,M]],  That=diag(J_4,I_4),
    Cgram_fg=<C_f,C_g>, M_fg=<D_f,D_g>, X_fg=<C_f,D_g>.

Here T has diagonal blocks I_2 and off-diagonal blocks J_2/2. The entire cross block X is retained.

The pointwise inequality of section 81.2 can retain the A deficit:

    ||(I-Q)D_f||_F^2 <= t_f+p-2 Re<S,C_f>.             (1)

For completeness, take any unitary U replacing H_f, and set

    C_U=A_f U^T/sqrt(2), D_U=A_f Z U^T/sqrt(2),
    N_U=conjugate(U) Z U^T.

The matrix N_U is traceless Hermitian unitary, D_U=C_U N_U, and ||C_U||_F^2=t_f. Thus

    ||(I-Q)D_U||_F^2 <= ||D_U-S N_U||_F^2
                     = ||C_U-S||_F^2
                     = t_f+p-2 Re<S,C_U>.

For H_f=L diag(s_1,s_2)V^*, 0<=s_j<=1, use the explicit unitary decomposition

    U_eta=L diag(eta_1,eta_2)V^*,
    q_eta=((1+eta_1 s_1)(1+eta_2 s_2))/4,
    H_f=sum_(eta in {+1,-1}^2) q_eta U_eta.            (2)

It is valid at zero or repeated singular values, after choosing any unitary SVD factors. Squared norm is convex and the overlap term is real-linear, proving (1). Summing gives

    sum_f ||(I-Q)D_f||_F^2 <= a-epsilon_A.             (3)

Let B_0:C^4->E_A tensor C^2 have columns D_f, let V have orthonormal columns spanning ker(QB_0), and set r=dim ker(QB_0), Pi=VV^*. Since dim L_S<=3, r>=1. For s=(1,1,1,1)^T/2 and Phat=diag(ss^*,Pi),

    Tr Phat(Khat-That)
       =-a+||B_0 V||_F^2-r
       =-a+||(I-Q)B_0 V||_F^2-r
       <=-a+||(I-Q)B_0||_F^2-r
       <=-r-epsilon_A.                               (4)

To apply this to the original maps, use the normalized reference input

    |Omega>=(1/sqrt(8))sum_(f,i)|f,i>_R tensor |f,i>_logical.

On the orthonormal joint reference/output support

    {|f,i>_R tensor |ff>_output},

the correct-output compression is K^T/8 and the target is T/8. The complementary actual block is positive of trace 1-TrK/8. Pinching into these two supports and positive-part duality imply

    delta >= (||K-T||_1+8-TrK)/8
          = Tr(T-K)_+/4
          >= (r+epsilon_A)/4.                        (5)

The physical Gram is transposed because K is the forward Gram. Transposition preserves the trace norm. This is a bound on the original leaking maps; no calibration or polar-replacement monotonicity is assumed.

Assume henceforth delta=1/4. Since r>=1 and epsilon_A>=0, every inequality in (3)--(5) that enters (4) must be an equality, r=1, and epsilon_A=0. Thus every t_f=1. Positivity of I_2-A_f^*A_f gives

    A_f^*A_f=I_2 for all f.                           (6)

For each |f,i>, its correct-output component already has norm one. Since the original Stinespring map is isometric, all wrong-output components vanish. Hence the original A channel is fibre-calibrated.

Rank(QB_0)=3, so rank Q=3. If rank S<=1, the space {S X:Tr X=0} has dimension at most two. Therefore

    rank S=2.                                       (7)

Let v be a unit vector spanning ker(QB_0), and write R_0=(I-Q)B_0. Equality in ||R_0 v||^2<=||R_0||_F^2 implies R_0(I-vv^*)=0. Set

    W=B_0 v=R_0 v,   ||W||_F^2=a.

Then the actual residual for fibre f is

    W_f=(I-Q)D_f=conjugate(v_f) W.                    (8)

Here W is again identified with its coefficient matrix. Since W is orthogonal to L_S,

    S^*W=lambda I_2                                 (9)

for some complex lambda: the orthogonal complement of all traceless 2-by-2 matrices is the scalar matrices.

### 82.3. Equality through every positive SVD component

Fix one fibre and its decomposition (2), retaining only positive weights. Equality in the pointwise bound (1) forces equality both in Jensen's inequality and in every positive-weight projection inequality. This can be seen directly by writing the pointwise slack as

    sum_eta q_eta ||(I-Q)D_Ueta-(I-Q)D_f||_F^2
      +sum_eta q_eta ||Q D_Ueta-S N_Ueta||_F^2.

Both sums are nonnegative, and their sum is zero. Consequently every positive component U satisfies

    (I-Q)D_U=W_f,   QD_U=S N_U,
    D_U=S N_U+W_f,
    C_U=S+W_f N_U.                                  (10)

By (6), each such C_U satisfies

    C_U^*C_U=I_2/2.                                 (11)

These are equality identities for every component in the stated SVD decomposition. There is no arbitrary replacement of H_f by a polar unitary.

### 82.4. Every original B correct-output block is unitary

All singular-value patterns in [0,1]^2 are handled as follows.

#### 82.4.1. Both singular values strictly below one

All four weights in (2) are positive, in particular a pair U and -U. Since D_(-U)=-D_U, their common residual in (10) is W_f=0. Equation (10) then gives C_U=S=C_(-U)=-C_U, forcing S=0. This contradicts (7). This also excludes both zero singular values and the cases with just one zero when the other is below one.

#### 82.4.2. Exactly one singular value is one

Suppose the other is strictly below one, including zero. Exactly two weights are positive; denote the two unitaries by U_+,U_-. Their sum and difference both have rank one. Since A_f is injective by (6), C_++C_- and C_+-C_- both have rank one.

Let N_+,N_- be their traceless Hermitian unitaries. Equation (10) yields

    C_+-C_-=W_f(N_+-N_-).

They cannot satisfy N_+=N_-, because C_+-C_- is nonzero. A nonzero traceless Hermitian 2-by-2 matrix has eigenvalues t,-t with t!=0, and is invertible. Therefore W_f has rank one. In particular v_f!=0, and (8) gives rank W=1 and a>0.

They also cannot satisfy N_+=-N_-: otherwise (10) would give C_++C_-=2S, contradicting rank S=2. Thus this fibre has two N matrices neither equal nor opposite.

From (9) and rank W=1, lambda=0. Put P=S^*S and R=W^*W, with rank R=1. For every fibre g and every positive component N in its SVD decomposition, equations (10)--(11) give

    P+|v_g|^2 N R N=I_2/2.                           (12)

Taking traces, using Tr R=a and p=1-a/4, yields |v_g|^2=1/4 for every g. Hence no coordinate vanishes, and

    N R N=4(I_2/2-P)                                 (13)

is one fixed nonzero rank-one matrix for all these N.

The following elementary qubit fact now applies. If two traceless Hermitian unitaries N_+,N_- are neither equal nor opposite, and both carry the same complex line span(w) to the same complex line span(u), then u is orthogonal to w. To verify this, choose w=e_0. Such a matrix has form

    N=[[b,z],[conjugate(z),-b]], b real, b^2+|z|^2=1.

Its first column is a unit vector on span(u). If u_0!=0, the requirement that its first entry be real fixes that column up to sign, and the rest of N is then fixed. This would give only one antipodal pair. Thus u_0=0, so u is orthogonal to w.

Apply this fact to the two matrices from the partially singular fibre, taking w in the range of R and u in the range of the fixed matrix in (13). Every positive-component N from every fibre must then have zero diagonal in the same basis. All such N lie in one real two-dimensional Pauli subspace, whose complex span also has dimension two. But (10) implies

    QD_g=S sum_eta q_eta N_(g,eta),

so rank(QB_0)<=2, contradicting rank(QB_0)=3.

#### 82.4.3. Both singular values are one

The two preceding cases exhaust every nonunitary 2-by-2 contraction. Hence each H_f is unitary. As in the argument for A, norm preservation of each correct-output block forces all original B wrong-output components to vanish. Both original maps are therefore fibre-calibrated.

The proof of B calibration did not infer absence of leakage merely from equality in trace-norm pinching; it used the equality identities for the actual contraction blocks.

### 82.5. Calibrated equality normal form and two normalized coherent tests

Write B_f=H_f and

    N_f=conjugate(B_f) Z B_f^T.

Each N_f is traceless Hermitian unitary. Equations (8)--(10) give

    C_f=S+conjugate(v_f)W N_f,
    D_f=S N_f+conjugate(v_f)W.                        (14)

Since rank S=2 and rank(QB_0)=3, the N_f span the full three-dimensional real Pauli space. A linear relation among Hermitian Pauli matrices has a real coefficient kernel, and its complexification is the complex coefficient kernel. Since that kernel is one-dimensional, v can be chosen real after a common phase change of v and W. Thus

    ||v||=1,  sum_f v_f N_f=0,
    C_f=S+v_f W N_f, D_f=S N_f+v_f W.                (15)

Retain S^*W=lambda I_2 and ||W||_F^2=a. Every C_f and D_f has norm one, so Cgram-J_4 and M-I_4 are trace zero.

Let |f,+>=(|f,0>+|f,1>)/sqrt(2) and |f,->=(|f,0>-|f,1>)/sqrt(2). The following two logical inputs are normalized:

    |psi_+>=(1/2)sum_f |f,+>,
    |psi_->=(1/2)sum_f |f,->.

Their physical product outputs, represented on the output MC support, are Cgram^T/4 and M^T/4; their target outputs are J_4/4 and I_4/4. From (15) and Tr N_f=0,

    (Cgram-J_4)s=-a s,  s=(1,1,1,1)^T/2,
    M v=a v.

For the first identity, sum C_f=4S and <C_f,S>=p; for the second, sum v_fD_f=W and <D_f,W>=a v_f. A trace-zero Hermitian matrix with eigenvalue q has trace norm at least 2|q|. Therefore these two normalized tests give

    delta>=a/2,   delta>=|1-a|/2.                    (16)

At delta=1/4 the only possible value is

    a=1/2,  p=7/8.                                  (17)

Now take the trace of C_f^*C_f=I_2/2 in (15). The mixed term vanishes because S^*W is scalar and N_f is traceless. Hence

    1=p+v_f^2 a.

Together with (17), this proves

    v_f=epsilon_f/2,  epsilon_f in {+1,-1}.           (18)

In particular every coordinate is nonzero; this conclusion is not assumed at any earlier division in the calibrated case.

### 82.6. The full negative-subspace invariance forces scalar matrix identities

Let Delta=Khat-That. Since both channels are now calibrated, Tr Delta=0. The normalized reference test and delta=1/4 imply ||Delta||_1<=2. The witness Phat=diag(ss^*,vv^*) from (4) has Tr Phat Delta=-1. Thus

    ||Delta||_1=2,   Tr Delta_-=1,
    -Tr Phat Delta=Tr Delta_-.

This optimality makes Phat an invariant subspace of the full Delta. Explicitly,

    Tr Phat Delta_+ + Tr(I-Phat)Delta_-=0.

Each term is nonnegative. Positivity therefore forces Phat Delta_+=0 and (I-Phat)Delta_-=0, so [Phat,Delta]=0. In particular the true cross block obeys

    Xv in span(s).                                  (19)

No cross coupling is discarded. Write R=W^*W and P=S^*S. Using sum v_fD_f=W gives

    (Xv)_f=<C_f,W>=2lambda+v_f alpha_f,
    alpha_f=Tr(N_f R),  alpha_f real.

By (19), v_f alpha_f is constant in f. Its sum is zero, since sum v_fN_f=0. Hence every v_f alpha_f=0. By (18), alpha_f=0 for every f. Since the N_f span all traceless Hermitian 2-by-2 matrices,

    R=(Tr R/2)I_2=I_2/4.                            (20)

Return to the full identity C_f^*C_f=I_2/2:

    P+v_f^2 N_f R N_f+2v_f Re(lambda)N_f=I_2/2.

Using (18)--(20), if Re(lambda) were nonzero, all v_f N_f would coincide, contradicting their three-dimensional span. Consequently

    Re(lambda)=0,   P=7I_2/16.                       (21)

The possible remaining imaginary overlap is excluded by a separate coherent test, rather than by an unproved reality convention.

### 82.7. A normalized mixed coherent test removes the remaining overlap

For complex alpha,gamma with |alpha|^2+|gamma|^2=1, use the normalized logical input

    |psi_(alpha,gamma)>
       =(1/2)sum_f [alpha|f,+>+gamma epsilon_f|f,->].  (22)

The actual output is E^T/4, where E is the forward Gram of

    e_f=alpha C_f+gamma epsilon_f D_f.

The target output is (|alpha|^2 J_4+|gamma|^2 I_4)/4. Both have trace one. Since sum epsilon_fN_f=0, equations (15) and (18) imply

    sum_f e_f=4alpha S+2gamma W.

Test the actual-minus-target difference on the normalized uniform output vector s. Its expectation is

    ||4alpha S+2gamma W||_F^2/16
       -|alpha|^2-|gamma|^2/4
      =-1/8+2 Re(conjugate(alpha) gamma lambda).      (23)

If lambda!=0, choose |alpha|=|gamma|=1/sqrt(2) and their relative phase so that conjugate(alpha)gamma lambda=-|lambda|/2. Then (23) is -1/8-|lambda|. A trace-zero Hermitian output difference has trace norm at least minus twice any negative expectation. Thus

    delta>=1/4+2|lambda|.

As delta=1/4, it follows that

    S^*W=0.                                        (24)

All input and output test vectors used here are normalized; no reference is required for these three coherent tests. The full reference test remains essential in section 82.6.

### 82.8. Exact Kraus rank and the minimal product

Equations (20)--(24) give

    S^*S=7I_2/16,   W^*W=I_2/4,   S^*W=0.           (25)

Hence S and W have rank two and orthogonal column ranges; their combined column span has dimension four. By (15), every C_f has its columns in this four-dimensional span. Since B_f is unitary and C_f=A_f B_f^T/sqrt(2), the columns of all A_f have the same collective span as all C_f. Conversely S is the mean of the C_f, while W=sum_f v_fD_f and D_f=C_fN_f, so the columns of S and W belong to that collective span. Therefore

    dim span{a_fi : f=1,...,4, i=0,1}=4.             (26)

For a calibrated Stinespring map V_A|f,i>=|f> tensor a_fi, the minimal environment dimension equals this record-span dimension: a linear combination of its environment-indexed Kraus operators vanishes exactly when the corresponding covector annihilates every a_fi. Thus the original channel A has Kraus rank exactly four.

Every local rank is at least two. An integer rank product below eight must be (2,2), (2,3), or (3,2), all excluded at exact quarter error by the theorem. The established marker construction of section 79 attains error 1/4 with ranks (4,2). Hence the least rank product at that exact error is eight.

As a qualitative corollary, the minimum error with rank bounds (3,2) or (2,3) is strictly greater than 1/4. Indeed the sets of finite-dimensional CPTP maps with those Kraus-rank upper bounds are compact (closed bounded Choi sets with closed rank constraints), and the error is continuous. The centroid-support lower bound is 1/4 throughout the set, and the equality case has just been excluded. This argument gives no numerical size for the strict gap.

### 82.9. The equality normal form is a fixed-marker construction

The original-channel rigidity proof in sections 82.2--82.8 supplies, for every original exact-quarter product with a rank-two B party, calibrated matrices

    C_f=S+(epsilon_f/2)W N_f,
    N_f=conjugate(B_f)Z B_f^T,
    epsilon_f in {+1,-1},   sum_f epsilon_f N_f=0,
    S^*S=7I_2/16,  W^*W=I_2/4,  S^*W=0.

Set U_0=4S/sqrt(7) and U_1=2W. They are isometries with orthogonal ranges. Since A_f=sqrt(2)C_f conjugate(B_f), its columns are

    a_fi=sqrt(7/8)U_0 conjugate(b_fi)
          +epsilon_f(-1)^i sqrt(1/8)U_1 conjugate(b_fi).

Identify their four-dimensional collective range with C^2 tensor C^2 by U_0 u=u tensor e_0 and U_1 u=u tensor e_1. This is a unitary identification on the minimal environment span, or an environment isometry in a larger presentation, and does not change the physical channel. Swap the two input bit labels in each fibre with epsilon_f=-1, simultaneously for both local maps. These independent bit swaps preserve the target, whose diagonal bit blocks are I_2 and whose off-diagonal bit blocks are J_2/2; hence they preserve the approximation error. After these swaps, the local records have the form

    a_fi=conjugate(b_fi) tensor m_i,
    m_i=sqrt(7/8)e_0+(-1)^i sqrt(1/8)e_1,
    <m_0,m_1>=3/4.                                  (27)

The overlap in (27) is the forward overlap <m_0,m_1>; because it is real, it agrees with section 79's reverse-overlap parameter as well. The corresponding traceless Hermitian unitaries are now N'_f=epsilon_f N_f and satisfy sum_f N'_f=0. Thus their Bloch axes n_f are balanced:

    ||n_f||=1,   sum_f n_f=0.                        (28)

Conversely (27) with any four qubit bases defines genuine calibrated Stinespring isometries. All subsequent norm assertions are on the resulting full physical product, allowing arbitrary reference systems.

### 82.10. Every balanced four-axis Gram has the disphenoid form

For vectors satisfying (28), put

    u=(n_1+n_2)/2,  v=(n_1+n_3)/2,  w=(n_1+n_4)/2.

Then

    n_1=u+v+w,  n_2=u-v-w,
    n_3=-u+v-w, n_4=-u-v+w.

Equality of their four squared lengths implies u dot v=u dot w=v dot w=0. Therefore, in an orthonormal real coordinate frame, their Gram is represented by

    n_1=(x,y,z), n_2=(x,-y,-z),
    n_3=(-x,y,-z), n_4=(-x,-y,z),
    x,y,z>=0,  x^2+y^2+z^2=1.                       (29)

Only the Gram is being specified; the orientation of this coordinate frame is immaterial. Write R_fg=n_f dot n_g. The four real characters of the Klein four group diagonalize R. Its eigenvalues are

    0, 4x^2, 4y^2, 4z^2,                            (30)

with the zero eigenvalue on the normalized uniform vector. In particular balance and uniform null coefficients do not force a regular tetrahedron.

### 82.11. Exact full-reference error of the entire balanced marker family

The two parties' qubit overlaps cancel their phases. At the real marker overlap 3/4, the plus/minus forward-Gram blocks are

    Cgram=(7/8)J_4+(1/8)R,
    M=(1/8)J_4+(7/8)R,
    X=0.                                            (31)

This identity holds also on the diagonal, because R_ff=1. Subtracting the target diag(J_4,I_4) leaves

    D_+=(R-J_4)/8,
    D_-=(J_4+7R)/8-I_4.                              (32)

The physical output uses the transpose of a forward Gram; the kernels in (32) are real symmetric, so their transposes coincide with them. The logical difference map is the sum of the Schur multiplier with kernel D_+ acting on the input's plus block and the Schur multiplier with kernel D_- acting on its minus block. Cross blocks are killed. For any normalized positive input with any reference, those two input principal blocks are positive and have traces summing to one. The triangle inequality therefore bounds the output error by the larger of the two Schur-multiplier diamond norms. Choosing an input entirely in one bit sector attains either sector norm, so the full norm is exactly their maximum. The fixed output MC isometry preserves it.

For any Hermitian Klein-circulant four-by-four kernel D with eigenvalues lambda_chi in its real character basis,

    D=(1/4)sum_chi lambda_chi h_chi h_chi^*,
    Schur_D=(1/4)sum_chi lambda_chi Ad_diag(h_chi).

Each h_chi has entries in {+1,-1}. The triangle inequality gives an arbitrary-reference upper bound sum|lambda_chi|/4. On the normalized uniform pure input, the output is D/4 and has exactly that trace norm. Hence

    ||Schur_D||diamond=||D||_1/4.                    (33)

Equations (30)--(32) give the eigenvalues

    D_+: -1/2, x^2/2, y^2/2, z^2/2;
    D_-: -1/2, (7/2)x^2-1, (7/2)y^2-1, (7/2)z^2-1.

Thus every balanced-marker member has exact error

    delta=max{1/4,
       [1/2+|(7/2)x^2-1|+|(7/2)y^2-1|
                    +|(7/2)z^2-1|]/4}.             (34)

The last three D_- eigenvalues sum to 1/2, so (34) equals 1/4 if and only if

    x^2>=2/7,  y^2>=2/7,  z^2>=2/7,
    x^2+y^2+z^2=1.                                  (35)

This is a nontrivial continuum. The regular tetrahedron is x^2=y^2=z^2=1/3, but, for example, x^2=3/10,y^2=13/40,z^2=3/8 also satisfies (35). Its nonzero Bloch-Gram eigenvalues are 6/5,13/10,3/2.

### 82.12. Classification and resource interpretation

By the original-channel rigidity proof above, every exact-quarter product having a rank-two party is, after an environment isometry and independent simultaneous bit swaps, one of the fixed-marker products (27) whose balanced-axis Gram satisfies (35). Conversely all these products attain exact quarter error. Their three axis directions are nonzero by (35), and the local ranks are exactly (4,2), consistently with the rigidity theorem.

No regular-tetrahedron uniqueness claim is made. The unrestricted optimum with both local ranks at least three remains open.

### 82.13. Attribution and boundary

The equality proof refines section 81's original-channel centroid-support witness by retaining the first party's trace deficit and following every equality through the SVD convex decomposition. It then uses three normalized coherent inputs together with the full normalized reference test. Section 79 supplies the original attaining product; sections 82.9--82.12 identify the complete rank-two-party equality family and its exact full-reference norm. The linear algebra, Stinespring equivalence, trace-norm duality, and channel-norm background are standard; see [Watrous, The Theory of Quantum Information, Chapters 1--3](https://cs.uwaterloo.ca/~watrous/TQI/).

No regular-tetrahedron uniqueness is asserted: the allowed disphenoids form a continuum. The minimum rank product eight is an original-channel statement, because both channels' calibration was proved from equality before the calibrated normal form was used. The classification is complete only when at least one party has local Kraus rank two. It does not classify quarter-error products whose two ranks are both at least three, or decide whether such products can beat quarter error. The unrestricted four-fibre optimum remains open in [sqrt(3)-3/2,1/4].

## 83. Transversal frame certificates and bilateral stability at quarter error

The bounds in this section are dimension-free and apply to original CPTP maps, allowing output leakage and arbitrary Kraus ranks on both sides. They give an exact global best-response obstruction when either party is fixed at its corresponding channel in a section-82 quarter-error equality pair. There is also a quantitative bilateral stability estimate. Neither result rules out simultaneous changes of both parties producing error below 1/4.

### 83.1. General transversal theorem for original channels

Let k>=2 be an integer and let F_(k,2):C^(2k)->C^k be the uniform qubit-fibre target

    F(|f,i><f,j|)=delta_ij |f><f|,
    F(|f,i><g,j|)=(1/2)|f><g|  for f!=g.

Fix the input and output MC encodings. For original CPTP maps A,B:C^(2k)->C^k, let

    delta=||(A tensor B)J_in-J_out F_(k,2)||diamond,

where the norm is unhalved and permits arbitrary references.

A transversal sigma=(i_1,...,i_k) selects one bit i_f in {0,1} from each fibre. For any Stinespring presentations, define the correct-output environment records

    a_f=(<f|_out tensor I)V_A|f,i_f>,
    b_f=(<f|_out tensor I)V_B|f,i_f>,
    G_sigma=(<a_f,a_g>)_(f,g),
    H_sigma=(<b_f,b_g>)_(f,g).

These are positive semidefinite Gram matrices, with diagonal entries at most one. Define

    L_A,sigma=||G_sigma||op,  L_B,sigma=||H_sigma||op,
    t_A,sigma=Tr G_sigma/k <=1,
    t_B,sigma=Tr H_sigma/k <=1.

These quantities are intrinsic to the original channels: the transposed Gram is the corresponding correct-output Choi compression, so changing or enlarging a Stinespring environment does not change them.

**Transversal bound.** For every transversal sigma,

    delta >= max{0,
       (k+1)/k - (2/k^2) Tr(G_sigma^T H_sigma)}        (1)

and consequently

    delta >= max{0,
       [k+1-2 L_A,sigma t_B,sigma]/k,
       [k+1-2 L_B,sigma t_A,sigma]/k}.                (2)

In particular, with

    L_* = min_(sigma, party in {A,B}) L_party,sigma,

one has

    delta >= max{0, [k+1-2L_*]/k}.                  (3)

The maximum with zero is explicit: a negative right-side expression is a vacuous certificate, not a negative error estimate.

#### 83.1.1. A normalized reference input and a full-output witness

Use the normalized reference input

    |Omega_sigma>=(1/sqrt(k))sum_f |f>_R tensor |f,i_f>_logical.

Let omega be its original product-channel output after the input MC encoding, and let tau be the target output. The orthonormal correct-output reference/output support has basis

    {|f>_R tensor |ff>_out : f=1,...,k}.

On this support the actual output compression is K_sigma^T/k, where K_sigma=G_sigma entrywise-multiplied by H_sigma. The target is entirely supported there, with coefficient matrix

    T_sigma/k,   T_sigma=(I_k+J_k)/2.

The form of T_sigma is the same for every transversal: between distinct fibres the target coefficient is 1/2 independently of the selected bits. The transpose occurs because the Grams are forward inner products.

The complementary actual block is positive and has trace 1-Tr K_sigma/k. Pinching therefore gives the valid original-channel bound

    ||omega-tau||_1
       >= [||K_sigma-T_sigma||_1+k-Tr K_sigma]/k
        = (2/k) Tr(T_sigma-K_sigma)_+.               (4)

For s=ones/sqrt(k), positive-part duality bounds the last expression below by

    (2/k)<s,(T_sigma-K_sigma)s>
      = (k+1)/k-(2/k^2)Tr(G_sigma^T H_sigma).         (5)

Transposition leaves this real uniform-vector Rayleigh value unchanged. This proves (1).

Equivalently, (5) is one explicit full-output trace-norm witness, without needing to pinch. Put

    |chi_sigma>=(1/sqrt(k))sum_f |f>_R tensor |ff>_out,
    Q_sigma=|chi_sigma><chi_sigma|,
    W_sigma=I-2Q_sigma.

The actual and target outputs have trace one, so W_sigma is a Hermitian contraction and

    Tr W_sigma(omega-tau)
       =2Tr Q_sigma(tau-omega)
       =(k+1)/k-(2/k^2)Tr(G_sigma^T H_sigma).         (6)

Thus the witness tests the full physical output, including any unpinched cross-sector coherences. It never assumes that these coherences vanish. The transversal input retains all cross-fibre coherences among its selected bits; no independent pairwise record replacement or unsupported two-test implication is used.

Since G_sigma^T is positive and G_sigma^T<=L_A,sigma I,

    Tr(G_sigma^T H_sigma) <= L_A,sigma Tr H_sigma.

Exchanging the two matrices gives the symmetric estimate. Substituting in (1) proves (2), and t_A,sigma,t_B,sigma<=1 proves (3).

### 83.2. Four-fibre exclusion criterion and robust frame excess

At k=4, the bound in section 83.1 yields

    delta >= max{0, 5/4-L_*/2}.                     (7)

In particular, any one party and any one transversal with Gram operator norm at most two certify delta>=1/4, irrespective of the other party's dimension, Kraus rank, phases, or output leakage.

A product with delta<=1/4-eta, eta>0, must satisfy

    L_A,sigma >=2+2eta,
    L_B,sigma >=2+2eta                               (8)

for every one of the 16 transversals. Thus all 32 party/transversal frame norms must exceed two for a strict improvement. This is a necessary condition only.

For a chosen party and transversal, write e=(L_party,sigma-2)_+. A weaker but convenient nonnegative-excess form of (7) is

    delta >= max{0, 1/4-e/2}.                       (9)

When L_party,sigma<2, the raw bound (7) is stronger than (9) and exceeds 1/4. No near-equality assumption is needed for either estimate.

### 83.3. Exact global best responses for every disphenoid equality member

Consider any original quarter-error pair (A_0,B_0) having a rank-two party. Exchange the parties if necessary so that B_0 has rank two. The classification in section 82 allows an environment isometry and independent simultaneous input-bit swaps to write its calibrated records as

    a_(f,i)^0=conjugate(b_(f,i)^0) tensor m_i,
    ||m_i||=1, <m_0,m_1>=3/4,
    N_f=conjugate(B_f^0)Z(B_f^0)^T,
    sum_f N_f=0.                                    (10)

The allowed disphenoids include every x^2,y^2,z^2>=2/7 with sum one. The following argument uses balance, not equal axis lengths.

For each fixed i in the relabelled coordinates, balance gives

    sum_f |conjugate(b_(f,i)^0)><conjugate(b_(f,i)^0)|
       =2I_2.

Conjugating gives the same tight-frame identity for b_(f,i)^0. Hence its four-vector Gram H_0 has nonzero eigenvalues 2,2 and satisfies

    H_0^2=2H_0,  Tr H_0=4,  ||H_0||op=2.

Because the marker is fixed within that bit sector and has norm one, the other party's Gram is G_0=conjugate(H_0)=H_0^T. Therefore

    ||G_0||op=||H_0||op=2,
    Tr(G_0^T H_0)=Tr(H_0^2)=8.                     (11)

In the original unpermuted labels, the two fixed-bit sets become two complementary transversals. This is why section 83.1 allows arbitrary transversals: the constant-bit Grams in the original labels need not themselves have norm two. The actual witness uses the corresponding selected input labels, so it does not require changing either physical channel.

It follows from (7) that

    delta(A_0,B)>=1/4  for every original CPTP B,
    delta(A,B_0)>=1/4  for every original CPTP A.     (12)

Since the partner (A_0,B_0) attains 1/4, the global best-response minimum in each line is exactly 1/4. In particular fixing the rank-four equality party blocks every unilateral escape that raises the other party's rank to three or higher, even with leakage. The second line is also consistent with section 81's original rank-two-party theorem.

The same one-party tight-frame certificate applies to any balanced fixed-marker construction with arbitrary unit markers: their overlap is irrelevant to the selected single-marker Gram. Quarter attainment, however, is being asserted here only for the classified equality family.

### 83.4. Bilateral stability for arbitrary original-channel perturbations

Fix a section-82 quarter-error equality pair (A_0,B_0), having one rank-two party, and fix one of its marker-aligned transversals in the original labels. For arbitrary original CPTP maps A,B of arbitrary ranks, denote the corresponding Grams by G,H and set

    DeltaG=G-G_0,   DeltaH=H-H_0.

The matrices DeltaG and DeltaH are Hermitian; they need not be positive or trace zero because the perturbed channels may leak. Define the real witness value

    g(A,B)=5/4-(1/8)Tr(G^T H).                      (13)

Equation (1) says delta(A,B)>=max{0,g(A,B)}. From (11), g(A_0,B_0)=1/4. The global best-response witness itself, not merely its optimized norm, satisfies

    g(A,B_0)>=1/4,  g(A_0,B)>=1/4.                 (14)

Indeed Tr(G^T H_0)<=2Tr G<=8, and similarly for the other term. Expanding the bilinear trace gives the exact identity

    g(A,B)=g(A,B_0)+g(A_0,B)-g(A_0,B_0)
              -(1/8)Tr(DeltaG^T DeltaH).

Therefore

    delta(A,B)>=max{0,
           1/4-(1/8)Tr(DeltaG^T DeltaH)}.            (15)

The trace in (15) is real but can have either sign. Hilbert--Schmidt Cauchy--Schwarz yields the explicit norm bound

    delta(A,B)>=max{0,
           1/4-||DeltaG||_F ||DeltaH||_F/8}.          (16)

There is also a channel-intrinsic estimate with no chosen Stinespring alignment. Put

    d_A=||A-A_0||diamond, d_B=||B-B_0||diamond.

Then

    delta(A,B)>=max{0,1/4-d_A d_B}.                  (17)

To prove (17), let E=A-A_0 and F=B-B_0, and apply E tensor F, with the reference unchanged, to the fixed encoded normalized input from section 83.1. Call the resulting Hermitian output Y. Both channel differences are trace-annihilating, so Tr Y=0. The cross term in (13) is precisely

    -2Tr(Q_sigma Y)=-(1/8)Tr(DeltaG^T DeltaH).

For a trace-zero Hermitian Y and a projection Q_sigma,

    |2Tr(Q_sigma Y)|<=||Y||_1.

The diamond-norm composition bound, or applying E and F successively with all other systems as references, gives

    ||Y||_1<=||E tensor F||diamond<=d_A d_B.

Combining this with (15) proves (17). The Gram and channel-distance bounds are both valid; one may use whichever is stronger. They are nontrivial only when their explicit right sides are positive.

Thus arbitrary sufficiently small simultaneous channel perturbations can improve quarter error by at most a product of their local sizes. A unilateral perturbation cannot improve it at all. This is a stability theorem for all original channels, not only calibrated perturbations or fixed-rank paths. It does not prove local minimality under simultaneous changes: a positive bilinear cross term in (15) is not excluded.

### 83.5. A stronger bound for local convex-noise perturbations

For the fixed equality pair of section 83.4, arbitrary original CPTP maps A_1,B_1, and 0<=epsilon,eta<=1, let

    A_epsilon=(1-epsilon)A_0+epsilon A_1,
    B_eta=(1-eta)B_0+eta B_1.

Then

    delta(A_epsilon,B_eta)>=max{0,1/4-epsilon eta}.   (18)

This is a single physical product of two local channels; it requires no shared randomness. Each local convex mixture can be represented by an orthogonal direct sum of local Stinespring environments.

For proof, use the same fixed input and witness g, rather than minimizing the norm independently for the four terms. Its values on (A_0,B_0), (A_1,B_0), and (A_0,B_1) are at least 1/4 by (11)--(14). On any original product output, the expectation of Q_sigma is at most one, whereas its target expectation is 5/8. Thus

    g(A_1,B_1)=2[5/8-Tr(Q_sigma omega_11)]>=-3/4.

Bilinearity of the physical product output now gives

    g(A_epsilon,B_eta)
       >= (1-epsilon eta)(1/4)+(epsilon eta)(-3/4)
        =1/4-epsilon eta,

which proves (18). This improves the factor-four estimate obtained from (17) and d_A<=2epsilon, d_B<=2eta.

If the two local direct-sum perturbations add equal new-environment amplitudes t, so epsilon=eta=t^2, the permitted improvement is at most t^4. This last interpretation has the explicit orthogonal-direct-sum scope. Arbitrary coherent Stinespring perturbations need not be such local mixtures, and are covered only by (15)--(17), not by an assumed mixture decomposition.

### 83.6. Boundary of the conclusion

The argument provides a full-output dual witness and exact global best-response certificates for every member of the disphenoid equality family. It permits arbitrary original leakage, dimensions, and both local ranks at least three in its comparisons. Its additional necessary condition for beating quarter is that all 32 party/transversal frame norms exceed two; its stability estimate requires both parties to change.

It does not prove a universal quarter lower bound. In particular one cannot infer that every pair of local frame collections has a transversal of norm at most two, nor that the bilinear term in (15) is nonpositive. The genuinely unrestricted four-fibre optimum remains open between sqrt(3)-3/2 and 1/4. No mean-rank-two assumption, polar-completion monotonicity, or false centroid/two-test variance bound is used.

## 84. Qubit-core Schur certificates for joint high-rank products

The theorem below certifies an entire two-sided class of original physical products, allowing arbitrary local Kraus ranks and output leakage. Both channels may change simultaneously. The hypothesis is a qubit-core factorization of either party's correct-output Gram, not a restriction of its actual Kraus rank. The robust bound measures distance from that factorization class. A concrete high-rank path shows that this obstruction is stronger than the section-83 transversal criterion even arbitrarily close to quarter-error equality.

This does not settle the unrestricted optimum or give a complete tangent-cone classification.

### 84.1. Original correct-output Grams and the factorization hypothesis

Let k>=4 be an integer, let F_(k,2) be the uniform qubit-fibre target with the fixed input/output MC encodings, and let A,B:C^(2k)->C^k be original CPTP maps. Let delta be their unhalved arbitrary-reference diamond error from that target. For Stinespring isometries of the original maps, form the correct-output records

    a_fi=(<f|_out tensor I)V_A|f,i>,
    b_fi=(<f|_out tensor I)V_B|f,i>.

Let G,H be their forward Grams, indexed by (f,i), and put K=G entrywise-multiplied by H. Their diagonal two-by-two blocks satisfy

    G_ff<=I_2,   H_ff<=I_2.

The target coefficient matrix T has diagonal blocks I_2 and off-diagonal blocks J_2/2.

Say that G has a qubit-core Schur factorization when

    G=Q entrywise-multiplied by M,
    Q>=0,  rank Q=2,  Q_ff=I_2,
    M>=0,  M_(fi,fi)<=1.                            (1)

A rank-two PSD matrix with Q_ff=I_2 is exactly the Gram of four, or generally k, orthonormal qubit bases u_f0,u_f1 in one common C^2. Factor M as a marker Gram. Thus (1) is equivalently a factorization of the correct-output record Gram by product vectors

    a_fi ~ u_fi tensor m_fi,
    <u_f0,u_f1>=0, ||u_fi||=1, ||m_fi||<=1.          (2)

The symbol ~ means equality of all inner products, or an isometric identification of the correct-output record spans. Markers may depend on both f and i, and may be subnormalized. Neither their dimension nor the original A environment dimension is bounded. The factorization does imply that this party's two correct-output columns within a fibre are orthogonal; it is not asserted for arbitrary correct-output blocks.

### 84.2. Exact dimension-free obstruction, including both-sided leakage

**Qubit-core transfer theorem.** If either G or H has (1), then

    delta >= (k-3)/k.                               (3)

In particular the original four-fibre error is at least 1/4, regardless of both actual local Kraus ranks, the other party's correct-output nonorthogonality, or either party's wrong-output components.

Proof. Suppose G=Q entrywise-multiplied by M, and define

    H'=M entrywise-multiplied by H.

Schur positivity gives H'>=0. Its diagonal fibre block is a contraction Gram, because

    H'_ff=M_ff entrywise-multiplied by H_ff
          <=M_ff entrywise-multiplied by I_2
           =diag(M_(f0,f0),M_(f1,f1)) <=I_2.         (4)

The first inequality follows by applying Schur positivity to M_ff and I_2-H_ff. Thus H' is the joint Gram of k arbitrary two-column contractions in a common finite environment. Algebraically its columns can be taken as m_fi tensor b_fi. All cross-fibre inner products are preserved, not fitted separately.

By associativity,

    K=Q entrywise-multiplied by H'.                 (5)

The section-81 contraction/support lemma applies directly to (5): one Gram consists of orthonormal qubit frames and the other has contraction diagonal blocks. Its full-matrix projection witness gives

    Tr(T-K)_+ >= k-3.                               (6)

For the original physical maps, the normalized input

    |Omega>=(1/sqrt(2k))sum_(f,i)|f,i>_R tensor |f,i>_logical

has correct-output compression K^T/(2k) on the orthonormal support

    {|f,i>_R tensor |ff>_out}.

The target compression is T/(2k), and the complementary actual block is positive with trace 1-Tr K/(2k). The valid original-output pinching inequality is therefore

    delta >= [||K-T||_1+2k-Tr K]/(2k)
          = Tr(T-K)_+/k.                            (7)

Combining (6) and (7) proves (3).

This proof transfers markers only in the algebraic Gram factorization used by the support lemma. It does not assume that arbitrary transferred contraction blocks assemble into a new output-dimension-k CPTP map with the same cross-fibre action. No such physical completion is needed: K in (5)--(7) is exactly the unchanged correct-output Gram of the original product, and the discarded trace is the original physical output deficit. The transpose is only the forward-Gram convention and does not affect trace norm. The parties can be interchanged.

Consequently joint deformations of qubit bases and arbitrary fibre-dependent markers cannot beat quarter error whenever at least one party retains (1). Such deformations need not preserve low local Kraus ranks. They need not retain the balanced axes or the fixed-marker assumption of the equality family.

### 84.3. A robust distance-to-factorization certificate

Let g be the diagonal of an actual correct-output Gram G. Define

    D_core(G)=min ||G-Q entrywise-multiplied by M||_1,

where the minimum runs over Q>=0 with rank Q=2 and Q_ff=I_2, and M>=0 with diag M=g. This set is nonempty: any common-qubit frame Gram Q and M=diag(g) are feasible. It is compact: both PSD factors have fixed bounded diagonals, and the rank-at-most-two condition is closed; Q_ff=I_2 forces rank exactly two. Thus the minimum is attained. A specific feasible pair Q,M is already a valid certificate; optimizing over Q is not asserted to be a convex problem.

**Robust factorization theorem.** For every original physical product,

    delta >= max{0, (k-3)/k-D_core(G)/(2k)},
    delta >= max{0, (k-3)/k-D_core(H)/(2k)}.          (8)

Proof. Fix any feasible Q,M, and write

    G_0=Q entrywise-multiplied by M,
    E=G-G_0,
    K_0=G_0 entrywise-multiplied by H,
    Delta=E entrywise-multiplied by H.

Then K=K_0+Delta. Equation (4) remains valid for M because its diagonal is g<=1, so the same algebraic contraction lemma gives Tr(T-K_0)_+>=k-3. Matching the diagonals makes E, and hence Delta, have zero diagonal and zero trace.

Schur multiplication by H is trace-norm contractive on Hermitian matrices because H>=0 and its diagonal entries are at most one. Indeed for the positive/negative decomposition E=E_+-E_-, both H entrywise-multiplied by E_+ and H entrywise-multiplied by E_- are positive, and their traces are at most Tr E_+ and Tr E_-, respectively. The triangle inequality gives

    ||Delta||_1<=||E||_1,
    Tr Delta_+=||Delta||_1/2.                        (9)

Apply the variational principle to an optimal projection for (T-K_0)_+:

    Tr(T-K)_+ >= Tr(T-K_0)_+-Tr Delta_+
               >= k-3-||E||_1/2.                   (10)

Using the original pinching (7) and minimizing ||E||_1 proves (8). No physical approximation channel with Gram G_0 is required.

At k=4, an error delta<=1/4-eta with eta>0 requires

    D_core(G)>=8eta,  D_core(H)>=8eta.               (11)

Thus a sub-quarter product must leave this factorization class on both sides by a definite, representation-independent Gram distance. The maximum with zero in (8) is essential when the displayed certificate becomes vacuous. The exact case D_core=0 is the qubit-core transfer theorem.

### 84.4. An explicit joint high-rank path missed by every transversal norm test

The following physical path has ranks (4,4) for every positive parameter, all 32 party/transversal Gram operator norms strictly greater than two, and error strictly above but converging to 1/4. It is nevertheless certified by the qubit-core transfer theorem throughout. This shows that the section-83 necessary spectral condition is not sufficient, even arbitrarily close to the equality family.

Start with the tetrahedral axes

    n_1=(1,1,1)/sqrt(3), n_2=(1,-1,-1)/sqrt(3),
    n_3=(-1,1,-1)/sqrt(3), n_4=(-1,-1,1)/sqrt(3).

Choose unitary qubit frames U_f whose column projectors are (I+(-1)^i n_f dot sigma)/2. For

    0<t<=1/100,
    D(t)=diag((1+i t)/(1-i t),1),

let U_f(t)=U_f for f=1,2,3 and U_4(t)=D(t)U_4. Write u_fi(t) for their columns. Choose fixed A markers and varying B markers

    m_0=e_0,  m_1=(3/4)e_0+(sqrt(7)/4)e_1,
    r_0(t)=e_0, r_1(t)=sqrt(1-t^2)e_0+t e_1.

Define calibrated Stinespring isometries on the complete local inputs by

    V_A(t)|f,i>=|f> tensor u_fi(t) tensor m_i,
    V_B(t)|f,i>=|f> tensor conjugate(u_fi(t)) tensor r_i(t).   (12)

Within each fibre the qubit columns are orthonormal; distinct fibres have orthogonal output labels. Thus these are actual CPTP maps for every stated t. Each party's correct-output Gram has (1), so (3) gives delta(t)>=1/4.

For each bit, the first three tetrahedral qubit records already span C^2. The two markers of A are independent, and those of B are independent for t>0. Each party's records therefore span exactly C^2 tensor C^2, so both minimal Kraus ranks are exactly four.

#### 84.4.1. Both constant-bit transversal norms are strictly above two

The new axes have sum n_4(t)-n_4, which is nonzero. Explicitly the phase in D(t) rotates about the z axis, and

    ||sum_f n_f(t)||
      =2sqrt(2/3)t/sqrt(1+t^2)>0.

For a fixed bit, the marker is the same unit vector in every fibre. The corresponding Gram has the same nonzero eigenvalues as the qubit frame operator. Hence, on each party and for both constant-bit transversals,

    L(t)=2+(1/2)||sum_f n_f(t)||>2.                 (13)

#### 84.4.2. Every mixed transversal retains a strict margin

First work at t=0 with arbitrary fixed markers of real overlap rho in [0,1]. A mixed transversal selects one or three copies of bit zero, or two copies.

If it selects one copy of one bit and three of the other, balance of the tetrahedral axes makes the sum of the three qubit projectors equal to I plus the selected single qubit projector. In the latter qubit line, the frame operator on the marker factor is P_m+2P_n. Its top eigenvalue is

    L_(1,3)(rho)=(3+sqrt(1+8rho^2))/2.              (14)

The perpendicular qubit line contributes only a unit marker projector, so (14) is the full top eigenvalue.

If it selects two copies of each bit, the two qubit frame operators coincide, by sum_f n_f=0. Each is I+v dot sigma with ||v||=1/sqrt(3). The full frame operator is their common qubit operator tensored with the sum of the two marker projectors, giving

    L_(2,2)(rho)=(1+1/sqrt(3))(1+rho).              (15)

For A at t=0, rho=3/4, and both (14)--(15) are strictly greater than 5/2. For B at t=0, rho=1, and they are at least three.

For any transversal, let V be its matrix of four unit environment columns. At the base, ||V||op<=2. If its perturbation is DeltaV, then

    ||V(t)^*V(t)-V(0)^*V(0)||op
       <=4||DeltaV||op+||DeltaV||op^2.              (16)

For A only the fourth column can change, and

    ||D(t)-I||op=2t/sqrt(1+t^2)<=2t.

Thus ||DeltaV_A||op<=2t and its Gram change is at most 8t+4t^2<1/2 on the stated interval. Every mixed A transversal consequently still has norm greater than two.

For B, the change of any marker vector has norm at most 2t, since

    ||r_1(t)-e_0||^2=2-2sqrt(1-t^2)<=2t^2.

The four marker changes contribute Frobenius norm at most 4t, and the one changed qubit column contributes at most 2t. Therefore ||DeltaV_B||op<=6t, and its Gram change is at most 24t+36t^2<1. Every mixed B transversal likewise retains norm strictly greater than two. Together with (13), all 32 norms exceed two for every 0<t<=1/100.

#### 84.4.3. Strict quarter gap and convergence

For this calibrated example only, there is also an explicit physical refactorization with the same complete encoded channel:

    V_At(t)|f,i>=|f> tensor u_fi(t) tensor m_i tensor r_i(t),
    V_Bt(t)|f,i>=|f> tensor conjugate(u_fi(t)).        (17)

Both maps in (17) are isometries. All product-record inner products, and thus every encoded matrix unit, coincide with (12). This is a constructed physical equivalence specific to (12), not the unneeded completion assumption excluded in section 84.2.

The second channel in (17) has rank two. The section-82 equality theorem would therefore require some signs epsilon_f in {+1,-1} such that sum_f epsilon_f n_f(t)=0. At t=0 every nonconstant sign pattern has norm at least two: a one-versus-three sign pattern gives norm two, and a two-versus-two pattern gives 4/sqrt(3). The perturbation of any such signed sum has norm at most ||n_4(t)-n_4||<=2t<2. Thus none becomes zero. The two constant sign patterns are nonzero by (13). No signed balance exists, so equality at 1/4 is excluded by section 82. Therefore

    delta(t)>1/4 for every 0<t<=1/100.              (18)

At t=0, (12) is the attaining tetrahedral 3/4-marker pair, so delta(0)=1/4. A quantitative continuity estimate is also available. The Stinespring operator changes satisfy

    ||V_A(t)-V_A(0)||op<=2t,
    ||V_B(t)-V_B(0)||op<=4t.

For B, split the change into a qubit rotation of norm at most 2t and a marker change of norm at most 2t; the unperturbed qubit columns are orthogonal. The standard pure-state trace-distance estimate followed by partial trace gives a local diamond distance at most twice the Stinespring operator distance. Tensoring channels and using the triangle inequality therefore yields

    1/4<delta(t)<=1/4+12t.                          (19)

In particular delta(t) converges to 1/4, although both ranks are four and every transversal norm test is already above its threshold for all t>0. The exact qubit-core factorization, not the transversal norm condition, supplies the lower certificate along this bilateral path.

### 84.5. Boundary

The proof uses Schur positivity and its trace-norm contraction consequence, the section-81 algebraic support witness, and the original reference/output pinching with its complete trace deficit. It does not claim that arbitrary local frames factor as a qubit core times markers. Nor does it complete arbitrary transferred contraction blocks into physical channels.

The two-sided path certifies a nontrivial family of simultaneous rank-raising directions, not the complete feasible cone around equality. Any sub-quarter product must fail the qubit-core factorization on both sides and satisfy the quantitative escape condition (11), in addition to the section-83 transversal conditions. General nonfactorizable bilateral deformations remain unresolved. The unrestricted four-fibre optimum remains open in [sqrt(3)-3/2,1/4].

## 85. Second-order stability against original bilateral rank-raising paths

This result does not assume a qubit-core factorization of either perturbed correct-output Gram. It concerns paths through any section-82 quarter-error equality pair having a rank-two party. Original output leakage and arbitrary finite environment dimensions are permitted.

The small parameter measures a smooth Stinespring amplitude. A channel mixture with new Kraus weight proportional to t generally has new-environment amplitude sqrt(t) and is not covered by the C^2-in-t hypothesis below. Nonnegative second-order curvature does not exclude higher-order improvement or imply full local minimality.

### 85.1. Statement

Let (A_0,B_0) be an original four-fibre quarter-error pair with B_0 of Kraus rank two. Use the environment isometries and independent simultaneous target-preserving bit swaps of section 82 to put the pair in marker-aligned coordinates:

    a_fi^0=conjugate(b_fi^0) tensor m_i,
    ||m_i||=1, <m_0,m_1>=3/4,
    sum_f |b_fi^0><b_fi^0|=2 I_2 for i=0,1.          (1)

The two original maps are calibrated by the equality theorem. Write B_i for the 2-by-4 matrix with columns b_fi^0 and put

    H_i^0=B_i^* B_i,  P_i=H_i^0/2.

Thus B_i B_i^*=2I_2 and P_i is a rank-two orthogonal projection.

Let A(t) be any family of original CPTP maps C^8->C^4 converging to A_0 as t goes to zero from above. Let B(t) admit a C^2 path of Stinespring isometries

    V(t):C^8 -> C^4 tensor (E_old direct-sum E_new),
    dim E_old=2,   V(0)=V_0 direct-sum 0,

where V_0 is a minimal Stinespring isometry of B_0. The fixed finite dimension of E_new is unrestricted. Set

    R=(I_out tensor P_new) V'(0).

For each bit i, let R_i:C^4->E_new have columns

    r_fi=(<f|_out tensor I_new)R|f,i>.

Define the squared wrong-output norm by

    ||R_wrong||_F^2
       =sum_(f,i) ||[(I_out-|f><f|) tensor I_new]R|f,i>||^2.

Let delta(t) be the unhalved arbitrary-reference diamond error of the original product A(t) tensor B(t) from the fixed RT target. Then

    delta(t) >= 1/4+c(R)t^2+o(t^2),

    c(R)=(1/8)[||R_wrong||_F^2
                  +sum_(i=0,1)||R_i(I_4-P_i)||_F^2] >=0.   (2)

Equivalently the asserted asymptotic lower bound means

    liminf_(t->0+) [delta(t)-1/4]/t^2 >= c(R).        (3)

If A(t)-A_0=O(t) in channel norm, for example if A(t) also has a C^2 Stinespring presentation, there are constants C and epsilon>0 such that

    delta(t) >= 1/4+c(R)t^2-Ct^3
    for 0<=t<=epsilon.                              (4)

In particular positive c(R) gives a strict error gap for all sufficiently small positive t, independently of the other party's allowed path. If c(R)=0, (2)--(4) do not exclude higher-order escape.

The conclusions are symmetric after exchanging the parties. For a general equality pair the coordinates used in (1) are obtained only by the allowed simultaneous swaps and fixed environment isometries; the theorem makes no unallowed rotation of the input-bit basis.

### 85.2. A rank-two Ky Fan consumer of the original contraction witness

For arbitrary original channels A,B define their correct-output record Grams G,H and K=G entrywise-multiplied by H, as in section 81. The target matrix T has diagonal two-by-two blocks I_2 and off-diagonal blocks J_2/2. For a Hermitian matrix Z, write Lambda_2(Z) for the sum of its two largest eigenvalues, and define

    f(A,B)=Lambda_2(T-K)/4.                          (5)

The original normalized reference input

    |Omega>=(1/sqrt(8))sum_(f,i)|f,i>_R tensor |f,i>_logical

has actual compression K^T/8 on the orthonormal support {|f,i>_R tensor |ff>_out}; the target compression is T/8. Retaining the complementary positive trace gives

    delta(A,B) >= Tr(T-K)_+/4 >= f(A,B).             (6)

This is an original-output pinching lower bound, not an assumption that good/bad cross coherences vanish. The forward-Gram transpose does not change eigenvalues. Both G and H depend real-linearly on their respective channels; in particular f is a function of the physical channels, independent of the chosen environments.

Whenever B has Kraus rank two, the section-81 support argument yields a rank-two projection witness, even if its nullspace has dimension larger than one. Here are the details of this refinement. For the original correct-output contraction blocks A_f and B_f, form

    C_f=A_f B_f^T/sqrt(2),
    D_f=A_f Z B_f^T/sqrt(2), Z=diag(1,-1),
    S=(1/4)sum_f C_f, a=4-4||S||_F^2.

Let Q project in coefficient-matrix space onto {SX:Tr X=0}. This space has complex dimension at most three. Section 81's pointwise contraction inequality gives

    sum_f ||(I-Q)D_f||_F^2 <=a.

Let D_col be the matrix with vectorized D_f as its four columns. Since rank(Q D_col)<=3, choose any unit vector v in ker(Q D_col). Then

    ||D_col v||^2=||(I-Q)D_col v||^2
                 <=sum_f||(I-Q)D_f||_F^2<=a.

In the full plus/minus coordinates, with s=ones/2, the plus Rayleigh value of K-T is -a and the minus Rayleigh value at v is at most a-1. Therefore the rank-two orthogonal projection diag(ss^*,vv^*) satisfies

    Tr diag(ss^*,vv^*)(Khat-That) <= -1.

The actual plus/minus cross block remains in Khat; its trace against this specified projection is zero, and no implication from separate scalar tests is used. Ky Fan's variational principle now gives

    Lambda_2(T-K)>=1,
    f(A,B)>=1/4 whenever B has Kraus rank two.        (7)

This holds for all original A, including arbitrary leakage and rank. Selecting one kernel vector is essential here: (7) is a statement about the two-largest-eigenvalue sum, not merely the full positive part.

### 85.3. Smoothness at every equality member, including boundary disphenoids

At the equality pair, section 82 gives balanced disphenoid parameters x^2,y^2,z^2>=2/7 with sum one. The eigenvalues of K_0-T in plus/minus coordinates are

    plus:  -1/2, x^2/2, y^2/2, z^2/2;
    minus: -1/2, (7/2)x^2-1, (7/2)y^2-1, (7/2)z^2-1.

Consequently the two largest eigenvalues of T-K_0 are both 1/2, and every other eigenvalue is at most zero. The two-dimensional cluster has a spectral gap of at least 1/2, even when one of the remaining eigenvalues is zero at a disphenoid boundary. The sum of the isolated top cluster is real-analytic in the Hermitian entries in a neighborhood of T-K_0; the degeneracy within the two-dimensional cluster causes no problem.

In the original bit coordinates after the allowed marker alignment, its spectral projection is

    P_0=(J_4/4) tensor I_2.                          (8)

Thus f is smooth near (A_0,B_0), f(A_0,B_0)=1/4, and its derivative is

    df=-(1/4)Tr(P_0 dK).                            (9)

There is also a useful global witness minimum with A_0 fixed. For an arbitrary original B, let H_i be the Gram of its four correct-output records in bit sector i. One has H_i>=0 and Tr H_i<=4. The aligned A_0 Gram obeys (G_i^0)^T=H_i^0=2P_i<=2I_4. Since Tr(P_0 T)=5,

    Tr(P_0 K)=(1/4)sum_i Tr(H_i^0 H_i)
                  <=(1/2)sum_i Tr H_i<=4,

and hence the rank-two variational principle gives

    f(A_0,B)>=Tr(P_0(T-K))/4>=1/4                  (10)

for every original B. This proof uses the fixed-bit tight frames in (1), which hold for every allowed disphenoid, not just the regular tetrahedron.

### 85.4. Polar separation of the old environment and the physical new-noise tangent

Decompose the perturbed isometry by its orthogonal environment sectors:

    V(t)=W(t) direct-sum R(t),
    R(t)=tR+O(t^2),
    W(t)^*W(t)=I_8-R(t)^*R(t).

The old block W(t) is square: its codomain has dimension 4 times 2=8. At t=0 it is the unitary V_0, so it is invertible for sufficiently small t. Its polar factor

    U(t)=W(t)[I_8-R(t)^*R(t)]^(-1/2)

is therefore an 8-by-8 unitary, with U(0)=V_0. Let Bbar(t) be the original CPTP map obtained by tracing the old two-dimensional environment of U(t). It has Kraus rank two and retains the original output dimension four. This is an actual physical comparison channel, constructed from the square old block; no arbitrary contraction-block completion is assumed.

Put D=R^*R. The C^2 hypothesis and the matrix square-root expansion imply, in any finite-dimensional channel norm,

    B(t)-Bbar(t)=t^2 Psi_R+O(t^3),

    Psi_R(X)=Tr_new(R X R^*)
                    -(1/2) B_0(DX+XD).              (11)

Indeed W(t)=U(t)[I-(t^2/2)D+O(t^3)], U(t)=V_0+O(t), and the environment-orthogonal old/new sectors contribute incoherently after partial trace. Wrong-output coherences within either sector are not discarded.

The coefficient Psi_R is a genuine one-sided physical tangent at B_0. For 0<=s<=||D||op^(-1), with the evident interpretation if D=0, the isometry

    V_s^R=V_0 sqrt(I_8-sD) direct-sum sqrt(s)R        (12)

defines an original CPTP map C_s satisfying C_0=B_0 and C'_0=Psi_R. Combining (10) with differentiability shows

    d_B f(A_0,B_0)[Psi_R]>=0.                       (13)

The polar factor is used solely to identify the rank-two comparison and the order-t^2 remainder. No monotonicity of the approximation error under polar replacement is asserted or needed.

### 85.5. Exact derivative and the flat new-environment directions

We now evaluate (13). For each fibre let B_f=[b_f0^0,b_f1^0] be the unitary base frame. In the auxiliary physical path (12), the derivative of the old correct-output column (f,i) is

    -(1/2)B_f D_ff e_i.

This follows from calibration of V_0: input components in any other fibre have an orthogonal output label. Let E_i be the 2-by-4 matrix with columns B_f D_ff e_i. The derivative of the bit-i correct-output Gram is then

    dot H_i=R_i^*R_i-(1/2)(B_i^*E_i+E_i^*B_i).       (14)

Using B_i B_i^*=2I_2 and <b_fi^0,B_f D_ff e_i>=D_(fi,fi), one obtains

    Tr(H_i^0 dot H_i)
       =Tr(H_i^0 R_i^*R_i)-2 sum_f D_(fi,fi).

Equations (8)--(9), with the forward-Gram identity (G_i^0)^T=H_i^0, therefore give

    d_B f[Psi_R]
       =-(1/16)sum_i Tr(H_i^0 dot H_i)
       =[2||R||_F^2-sum_i Tr(H_i^0 R_i^*R_i)]/16
       =[||R_wrong||_F^2
                     +sum_i||R_i(I_4-P_i)||_F^2]/8
       =c(R).                                      (15)

All traces here are real. Orthogonality of the correct/wrong output projections on each column gives ||R||_F^2=||R_wrong||_F^2+sum_i||R_i||_F^2; H_i^0=2P_i then gives the last equality. This calculation independently exhibits the nonnegativity required by the physical tangent argument.

The exact zero-coefficient condition is

    c(R)=0 iff R_wrong=0 and R_i=R_iP_i for i=0,1.   (16)

Equivalently, there must be two common, bit-dependent linear maps L_i:C^2->E_new such that

    r_fi=L_i b_fi^0 for every f,
    L_i=(1/2)R_i B_i^*.                             (17)

Indeed R_iP_i=R_i is equivalent to R_i=(R_i B_i^*/2)B_i. These are conditions on the first-order new-environment amplitude only. They neither impose a full finite-t qubit-core factorization nor classify the possible higher-order path. No conclusion that all flat directions are harmless is made.

### 85.6. Completion of the asymptotic proof

By (7), f(A(t),Bbar(t))>=1/4 for every sufficiently small t. Smoothness from section 85.3, convergence A(t)->A_0 and Bbar(t)->B_0, and (11) imply

    f(A(t),B(t))-f(A(t),Bbar(t))
       =t^2 d_B f(A_0,B_0)[Psi_R]+o(t^2)
       =c(R)t^2+o(t^2).                             (18)

For precision, this follows by integrating the derivative of the smooth function f along the line segment between Bbar(t) and B(t). Its derivative converges uniformly on that segment to d_B f(A_0,B_0), while the channel difference is t^2 Psi_R+O(t^3). The segment consists of CPTP maps, and in any case f is defined smoothly on a neighborhood in the ambient Hermitian coefficient space.

Combining (6), (7), and (18) proves (2)--(3). If A(t)-A_0=O(t), then Bbar(t)-B_0=O(t) and the smooth derivative is locally Lipschitz. The error in replacing it by its value at the base is O(t) times O(t^2), and the remainder in (11) is O(t^3). This proves (4).

### 85.7. Interpretation and boundary

The result includes arbitrary coherent first-order changes inside the old two-dimensional environment, arbitrary first-order output leakage, arbitrary finite rank-raising new-environment directions, and simultaneous changes of the other original channel. It requires neither qubit-core factorization of the perturbed Grams nor their calibration. The square old-sector polar factor is available because a rank-two channel C^8->C^4 has a unitary minimal Stinespring isometry.

New-environment leakage or failure to preserve either tight-frame row space forces a positive quadratic gap. Only the explicitly identified directions (16)--(17) can remain flat to this order. Even in that flat class, a smooth bilateral path can at most improve by o(t^2), or by O(t^3) under the Lipschitz condition. These statements concern the smooth amplitude parameter, and do not apply after a singular reparameterization t=sqrt(s) as if the same differentiability hypothesis held in s.

This is a second-order obstruction, not a complete feasible-cone or local-minimum theorem. Higher-order nonfactorizable bilateral escape and the unrestricted quarter-optimum problem remain open.

## 86. Local quartic stability from the rank-two Ky Fan minimum manifold

The present argument strengthens the second-order theorem in section 85. It concerns arbitrary original CPTP maps C^8 -> C^4 near any section-82 quarter-error pair having a rank-two party. Both perturbed channels may have arbitrary Kraus rank and output leakage. No differentiable path, calibrated perturbation, or qubit-core factorization is assumed in the main statement.

The conclusion permits improvement at fourth order in a smooth new-environment amplitude. It does not prove a local minimum or settle the unrestricted optimum.

### 86.1. Statement and conventions

Let (A_0,B_0) be any original quarter-error pair with B_0 of Kraus rank two. Write J_B for the unnormalized Choi matrix of B, so J_B is positive semidefinite and Tr J_B=8. List its eigenvalues in nonincreasing order and define

    epsilon_2(B)=sum_(j=3)^32 lambda_j(J_B).                 (1)

There exist a neighborhood U of (A_0,B_0) in the finite-dimensional space of original channels and a finite constant C such that

    delta(A,B) >= 1/4-C epsilon_2(B)^2
    for every (A,B) in U.                                  (2)

Here delta is the unhalved arbitrary-reference diamond error of the original product from the fixed RT target. The roles of the parties can be exchanged. Since delta is nonnegative, the right side may also be replaced by its maximum with zero.

A Stinespring version is useful. Fix any finite environment dimension d>=4 for A and an old environment of dimension two for B. Embed the equality isometries in these environments. For any nearby isometries V_A and

    V_B=W direct-sum R,
    W:C^8 -> C^4 tensor C^2,

there is a local constant C_d such that

    delta(A,B) >= 1/4-C_d ||R||_F^4.                        (3)

The constant can be chosen independently of the finite dimension of the new environment containing R. Equation (2) follows by taking d=32 and making a canonical Choi spectral split.

Consequently, along any path converging to the equality pair and possessing a Stinespring split with ||R(t)||_F=O(t), one has delta(t)>=1/4-O(t^4). The other party need only converge to A_0. In particular the O(t^3) possible improvement left by section 85 is excluded, including its flat-curvature directions. If new Kraus probability rather than amplitude is the parameter, (2) instead gives a quadratic bound in that tail probability.

All inner products below are conjugate-linear in the first argument. Gram matrices are forward Grams. Correct-output blocks are denoted A_f and B_f, with two columns indexed by the fixed input bit. The only bit changes used at the base are the simultaneous fibrewise swaps allowed in section 82.

### 86.2. The smooth rank-two comparison function

For the correct-output Grams G,H put K=G entrywise-multiplied by H. The target T has diagonal 2-by-2 blocks I_2 and off-diagonal blocks J_2/2. Define

    F(A,B)=Lambda_2(T-K)/4,                                (4)

where Lambda_2 sums the two largest Hermitian eigenvalues. On the normalized reference input 8^(-1/2) sum_(f,i)|f,i>_R|f,i>_logical, the correct joint reference/output compression is K^T/8 on {|f,i>_R tensor |ff>_out}. Pinching and retaining the complementary positive trace give

    delta(A,B)>=Tr(T-K)_+/4>=F(A,B).                        (5)

The section-85 refinement of the original contraction/support witness gives

    F(A,B)>=1/4 whenever B has Kraus rank two,              (6)

for every original A, including leakage. Explicitly, with C_f=A_f B_f^T/sqrt(2), D_f=A_f Z B_f^T/sqrt(2), S=mean_f C_f and Z=diag(1,-1), project onto {SX:Tr X=0}. Its complex dimension is at most three. A unit vector in the kernel of the four projected D columns, together with the uniform plus vector, gives a rank-two projection of T-K with trace at least one. Only one kernel vector is selected, even if the kernel is larger.

At any section-82 equality member the two largest eigenvalues of T-K are 1/2,1/2; the others are at most zero. Thus the top cluster has a gap at least 1/2, including boundary disphenoids. In marker-aligned bit coordinates its projection is

    P_0=(J_4/4) tensor I_2.                                (7)

The function F is real-analytic near the base in the ambient real channel coordinates. We also view it as a smooth function of Stinespring isometries. The comparison space is

    X=St(C^8,C^4 tensor C^d) times U(8),

where the second factor is traced over an environment of dimension two. By (6), F>=1/4 everywhere on X. Both correct and wrong output blocks are retained in this space.

We prove a quadratic growth estimate on X about an explicit smooth minimum manifold M. This intermediate manifold consists of minima of F; it is larger than the quarter-error equality family of the full diamond norm.

### 86.3. An explicit nearby minimum manifold

At the base, the calibrated B blocks B_f are 2-by-2 unitaries. Set

    N_f=conjugate(B_f) Z B_f^T.

These are traceless Hermitian unitaries. After the allowed marker alignment, sum_f N_f=0, and their real span is the full three-dimensional Pauli space. This span condition holds at every allowed disphenoid, since x^2,y^2,z^2>=2/7.

For nearby calibrated B frames satisfying sum_f N_f=0, take d-by-2 matrices S,W and real parameters h,beta near 1/2,0 such that

    S^*S=(1/2-h/8)I_2,
    W^*W=(h/2)I_2,
    S^*W=i beta I_2.                                      (8)

Define calibrated A frames through

    C_f=S+(1/2)W N_f,
    A_f=sqrt(2) C_f conjugate(B_f).                        (9)

Equations (8) imply C_f^*C_f=I_2/2 and hence A_f^*A_f=I_2. Make both original isometries calibrated by assigning output f to the two columns of fibre f. Let M be the resulting local subset of X.

Here is a local parameterization and a check of smoothness. The Gram matrix of [S W] is

    [[1/2-h/8, i beta],[-i beta,h/2]] tensor I_2.

It is positive definite at and near the base. Thus [S W] is parameterized by an arbitrary F_4 in St(C^4,C^d), multiplied on the right by the positive square root of this Gram matrix. The balance map (B_f)_f -> sum_f N_f has surjective differential at the base: each N_f can vary over its Bloch-sphere tangent plane, and a real vector orthogonal to all four such tangent planes would be parallel to every Bloch axis, which is impossible. Its zero set is therefore smooth of real dimension 16-3=13. Together with h,beta and dim_R St(C^4,C^d)=8d-16, the parameter space has dimension

    dim_R M=8d-1.                                        (10)

It is locally embedded. Indeed B_f are part of the tuple; C_f are recovered from A_f,B_f; balance gives S=mean C_f and W=(1/2)sum_f D_f, where D_f=C_f N_f. Finally h=||W||_F^2 and beta=Im Tr(S^*W)/2, and the Stiefel parameter is recovered by the inverse Gram square root.

Every point of M is a minimum of F. In full plus/minus coordinates the subspace spanned by (s,0),(0,s), with s=ones/2, is invariant under T-K. Its compression is

    [[h,-4i beta],[4i beta,1-h]],                          (11)

which has trace one. The other six eigenvalues remain separated below this cluster after shrinking the neighborhood, by the base gap. Hence F=1/4 on M and its top projection is P_0.

A further property of M will be important. Let

    T_i=sqrt(2)[S+(-1)^i W/2].

Then T_i^*T_i=I_2 and a_fi=T_i conjugate(b_fi). The balance condition implies sum_f |b_fi><b_fi|=2I_2 separately for both fixed bits. Thus, for each (A_m,B_m) in M, the bit-i Gram of A_m is the transpose of a rank-two tight-frame Gram H_i^m with H_i^m<=2I_4. For every original channel B with correct bit Gram H_i,

    Tr(P_0 K)=(1/4)sum_i Tr(H_i^m H_i)
                  <=(1/2)sum_i Tr H_i<=4,
    Tr(P_0 T)=5.

Consequently

    F(A_m,B)>=1/4 for every original B.                    (12)

This remains true when h and beta differ from their equality values. Their scalar cross overlap is T_0^*T_1=(1-h/2-2i beta)I_2; no assertion of full diamond equality for these additional parameters is made.

### 86.4. Exact sum of squares on the calibrated comparison subspace

Consider a calibrated comparison tuple near the base, without assuming balance or (8). Put C_f=A_f B_f^T/sqrt(2), D_f=C_f N_f and S=mean C_f. Let Q be the orthogonal projection in matrix Hilbert space onto

    L_S={SX:Tr X=0}.

Near the base S has full column rank, so dim_C L_S=3. Let D_col have the vectorized D_f as columns. At the base QD_col has rank three, because its columns are S N_f and the N_f span Pauli space. Therefore there is a smooth unit vector v spanning ker(QD_col), fixed by requiring <s,v> to be positive real. Set

    W=D_col v,
    E_f=Q D_f-S N_f,
    R_c=(I-Q)D_col,
    P_w=diag(ss^*,vv^*)                                  (13)

in plus/minus coordinates. In particular S^*W is a scalar matrix, since W is orthogonal to L_S.

Since each N_f is unitary, C_f^*C_f=I_2/2 and S is the mean,

    a=4-4||S||_F^2=sum_f||C_f-S||_F^2
       =sum_f||D_f-SN_f||_F^2
       =sum_f||E_f||_F^2+||R_c||_F^2.

Moreover D_col v=R_c v. The plus uniform Rayleigh value of T-K is a and the minus value at v is 1-||D_col v||^2. Hence the exact identity is

    4(F-1/4)
      =sum_f||E_f||_F^2+||R_c(I-vv^*)||_F^2
         +[Lambda_2(T-K)-Tr(P_w(T-K))].                   (14)

No plus/minus cross block has been removed. Its effect appears in the final variational gap.

Write P_* for the true top-two spectral projection. In a fixed small neighborhood there are constants 0<gamma<=Gamma such that

    (gamma/2)||P_*-P_w||_F^2
      <=Lambda_2(T-K)-Tr(P_w(T-K))
      <=(Gamma/2)||P_*-P_w||_F^2.                         (15)

Indeed diagonalize T-K and use the separation of its second and third eigenvalues for the lower bound and its spectral diameter for the upper bound; the exchanged projection weight is 2-Tr(P_*P_w)=||P_*-P_w||_F^2/2.

At the base all three nonnegative terms in (14) vanish. Therefore a calibrated tangent is in the kernel of the Hessian of F precisely when

    E_f'=0 for every f,
    [R_c(I-vv^*)]'=0,
    P_*'=P_w'.                                           (16)

This equivalence uses both bounds in (15) and smoothness. Hessians are regarded as real quadratic forms.

### 86.5. The Hessian kernel is exactly T M

We now calculate every implication in (16). Primes denote derivatives at the base along any smooth calibrated curve. There v=s, S^*W=0, W^*W=I_2/4 and ||W||_F^2=1/2. The first two conditions in (16) imply

    D_f=S N_f+conjugate(v_f)W+O(t^2),
    C_f=S+conjugate(v_f)W N_f+O(t^2).                     (17)

Since D_col v=W and v is unit, substitution in the first equation gives S sum_f v_f N_f=O(t^2). As S has full column rank,

    sum_f v_f N_f=O(t^2).

Its imaginary first derivative yields sum_f Im(v_f')N_f=0. The only real relation between the four base N_f is the uniform one. The phase convention gives sum_f Im(v_f')=0, so Im(v_f')=0 for all f. The normalization of v gives sum_f Re(v_f')=0.

The exact identity S^*W=lambda I_2 and tracelessness of N_f eliminate the cross term in the Frobenius norm of the second equation in (17). With p=||S||_F^2 and w=||W||_F^2,

    1=p+|v_f|^2 w+O(t^2).

Summing derivatives gives 4p'+w'=0. Each individual derivative is p'+w'/4+w_0 Re(v_f')=0, and w_0=1/2. Thus v'=0. The differentiated relation above then gives

    sum_f N_f'=0,
    P_w'=0,
    P_*'=0.                                              (18)

The last conclusion is where the full variational gap is essential. Differentiating spectral invariance, P_*'=0 implies

    (I-P_0)(T-K)'P_0=0.

Use its plus-orthogonal/minus-uniform component. If X=C_col^*D_col is the full cross Gram block, then Xv has f-th entry <C_f,W>. Equations (17) give

    (Xv)_f=2lambda+v_f Tr(N_f W^*W)+O(t^2).

Because v'=0 and W^*W=I_2/4 at the base, cross invariance says the four numbers Tr(N_f (W^*W)') are equal. Their sum is zero by balance, so they are all zero. The N_f span Pauli space; therefore (W^*W)' is scalar.

Finally differentiate the individual matrix normalizations C_f^*C_f=I_2/2 using (17). They give

    (S^*S)'+(1/4)(W^*W)'+Re(lambda')N_f=0.

Averaging and then subtracting shows that (S^*S)' is scalar, equals -(W^*W)'/4, and Re(lambda')=0. Together with (18), these are exactly the tangent constraints of (8)--(9):

    (W^*W)'=(h'/2)I_2,
    (S^*S)'=-(h'/8)I_2,
    (S^*W)'=i beta' I_2,
    sum_f N_f'=0,
    C_f'=S'+(W'N_f+WN_f')/2.                             (19)

There are no omitted singular support cases: S and [S W] have full respective ranks two and four throughout the chosen neighborhood, and every base disphenoid spans all three Pauli directions. The parameterization in section 86.3 realizes all derivatives satisfying (19), because the positive-definite Gram constraint is a smooth Stiefel parameterization and balance is a regular constraint. Thus every calibrated Hessian-kernel vector lies in T M. Conversely F is constant and minimal on M, so every tangent to M is in the Hessian kernel.

### 86.6. Original output leakage and normal quadratic growth

The previous computation extends to the full comparison space X; it does not assume perturbations remain calibrated. At a calibrated base isometry the correct-output part of any tangent satisfies the individual Stiefel tangent equations. Choose a calibrated curve with these same correct-output first derivatives. For the B side choose the corresponding block-diagonal unitary curve. Such a choice is possible because the first derivative of each correct block is tangent to its local frame manifold. The original full tangent may also have wrong-output blocks.

The first derivative of F with respect to arbitrary variations of the correct records at the base is

    dF=-(1/4)sum_(f,i) Re[<a_fi^0,da_fi>
                                +<b_fi^0,db_fi>].          (20)

To check this, dF=-(1/4)Tr(P_0 dK), and in either fixed-bit sector the other party's tight Gram sends the base record-column matrix to twice itself. Differentiating the Gram gives Tr(P_0 dK)=sum Re of the displayed record inner products. Wrong-output records do not enter K and have zero direct first derivative.

Write a curve as V_0+tV_1+t^2 V_2+o(t^2), without a factorial in V_2. Comparing its isometry normalization with that of the calibrated curve having the same correct V_1 gives, fibrewise,

    A_f^0{}^* Delta A_(2),f+Delta A_(2),f^* A_f^0
       =-sum_(g!=f) L_(g f)^* L_(g f),

where L_(g f) are the first-order wrong-output blocks; the same identity holds for B. All mixed second-derivative terms of F agree between the two curves because their correct first derivatives agree. Equation (20) therefore gives for the t^2 coefficients

    q_full=q_calibrated
              +(||L_A||_F^2+||L_B||_F^2)/8.              (21)

This includes arbitrary environment components of the A tangent; those inside the correct output blocks were already included in the d-dimensional calibrated calculation. The full comparison Hessian is positive semidefinite by (6). Equation (21) shows that its kernel forces both wrong-output tangents to vanish and then is exactly the calibrated kernel T M. Hence

    ker Hess_X F at the base = T M.                       (22)

This proves the needed local quadratic growth by an elementary normal-coordinate argument. The Hessian is positive definite on the normal space to M at the base. The same lower bound, with a possibly smaller positive constant, holds on normal spaces at nearby points of M by continuity. Both F=1/4 and dF=0 on M. Taylor expansion in tubular normal coordinates, uniformly on a small neighborhood, consequently gives

    F(x)>=1/4+c rho(x)^2,   c>0,                          (23)

where rho(x) is the distance to M in any fixed smooth local metric on X. Equivalently this is a local Morse--Bott minimum. No general Morse--Bott theorem is required beyond the stated normal-coordinate Taylor argument.

### 86.7. Comparing an arbitrary rank-raising channel to M

For a nearby full B isometry write V_B=W direct-sum R, D=R^*R, epsilon=||R||_F^2. Since the old sector W is square and near a unitary, its polar factor

    U=W(I-D)^(-1/2)

is unitary. Thus V_B=U sqrt(I-D) direct-sum R. Let B_U denote its rank-two old comparison channel, and x=(V_A,U) in X. The square-root expansion gives, uniformly for small epsilon,

    B-B_U=Psi_(U,R)+O(epsilon^2),
    Psi_(U,R)(Y)=Tr_new(R Y R^*)
                    -(1/2)B_U(DY+YD),
    ||Psi_(U,R)||<=C_1 epsilon.                           (24)

These channel-norm estimates depend on the fixed input/output dimensions, not on the dimension of the new environment. For example ||D||op<=epsilon and the new CP map has norm bounded by a fixed constant times epsilon; the old square-root remainder is O(||D||op^2).

Let m=(V_(A_m),U_m) be a nearby closest point of M. At m the physical one-sided path

    U_m sqrt(I-sD) direct-sum sqrt(s)R,   s>=0,

is an isometry for sufficiently small s. Its channel derivative is Psi_(U_m,R). The fixed-A_m global minimum (12) and differentiability of F imply

    d_B F(A_m,B_(U_m))[Psi_(U_m,R)]>=0.                    (25)

Smoothness and (24) imply a uniform Lipschitz comparison

    d_B F(A,B_U)[Psi_(U,R)]>=-C_2 rho(x) epsilon.           (26)

Indeed the derivative of F varies by O(rho), while Psi varies with U by O(||U-U_m|| epsilon); both changes are bounded using (24). Taylor expansion in the physical channel difference in (24), followed by (23), gives

    F(A,B)>=1/4+c rho^2-C_2 rho epsilon-C_3 epsilon^2
           >=1/4-C_4 epsilon^2.                          (27)

The final inequality completes the square. Combining (5) and (27) proves (3). No error monotonicity under polar replacement is used. The argument keeps all original output coherences; pinching is used only for the valid lower bound (5).

### 86.8. Intrinsic Choi-tail form and path consequence

At B_0 the two nonzero Choi eigenvalues are 4,4: the eight base correct records are four orthonormal qubit frames. Thus there is a spectral gap separating the top-two Choi subspace from the rest. Near B_0 let P_B be its spectral projection. Choose a continuous orthonormal frame E_B:C^2->C^32 for that subspace, aligned with the base Kraus vectors. The Choi vector columns

    J_B^(1/2) E_B,
    J_B^(1/2)(I-P_B)

form an old/new Kraus decomposition. Their Gram outer-product sum is J_B because P_B commutes with J_B. After the usual vector-to-Kraus reshaping, its Stinespring isometry has an old square block W near V_0 and a new block R satisfying

    ||R||_F^2=Tr[J_B(I-P_B)]=epsilon_2(B).                 (28)

The old frame can be aligned at the base by a fixed environment unitary. For A use the canonical square-root Choi decomposition in environment dimension 32; it is continuous near A_0, and a fixed environment unitary identifies its base with an embedding of the original four-dimensional equality environment. Therefore every pair of physical channels in a sufficiently small neighborhood has a lift to the Stinespring neighborhood used in (3), with d=32. This proves (2) without a smooth-path assumption.

Alternatively, for any given Stinespring split the rank-two old Kraus contribution is positive semidefinite and leaves a positive Choi remainder of trace ||R||_F^2. The variational characterization of the two largest Choi eigenvalues gives epsilon_2(B)<=||R||_F^2. Hence amplitude ||R(t)||_F=O(t) implies the stated quartic path lower bound. In particular a C^2 finite-environment path covered by section 85 has this property. Arbitrary convergence of the other channel suffices for eventual membership in U.

The theorem is local in channel space and its constant need not be uniform over the entire equality family. The second-order positive coefficient of section 85 can still provide a stronger positive gap in nonflat directions. In the flat directions, the present estimate rules out cubic improvement but leaves quartic and higher-order escape unresolved. The unrestricted quarter-optimum conjecture remains open.

## 87. Exact anisotropic quartic coercivity at every disphenoid equality pair

This is a sequel to the local Choi-tail bound in section 86, not a modification of that result. We compute the complete minimized probability-quadratic coefficient of the rank-two Ky Fan witness, including all original-channel comparison tangents. We then give a separate physical C²-amplitude-path consequence. The result excludes negative fourth-order coefficients along those paths; it does not prove a local minimum, exclude higher-order escape, or settle the unrestricted product optimum.

All environments in the path statement are fixed and finite. A path with new Kraus probability proportional to its parameter generally has amplitude proportional to the square root of that parameter and is not a C² amplitude path at zero.

### 87.1. Statement and original-channel consumer

Let (A₀,B₀) be any section-82 original quarter-error pair, with B₀ of Kraus rank two. Use its allowed simultaneous fibrewise bit swaps and fixed environment isometries to put it in marker form. Write

\[
 N_f=\overline {B_f}ZB_f^T
     =\sum_{a=1}^3 n_a\chi_a(f)\sigma_a,
 \qquad u_a=n_a^2,\quad \sum_a u_a=1,\quad u_a\ge2/7.       \tag{1}
\]

Here Z=diag(1,−1), the σ_a are the standard Pauli matrices, n_a>0, and the four characters are

\[
 \chi_0=(1,1,1,1),\quad \chi_1=(1,1,-1,-1),\quad
 \chi_2=(1,-1,1,-1),\quad\chi_3=(1,-1,-1,1).              \tag{2}
\]

Each u_a lies in [2/7,3/7]. The coefficient matrices at the base can be chosen as

\[
 C_f=A_fB_f^T/\sqrt2={1\over4}
       \begin{bmatrix}\sqrt7 I_2\\N_f\end{bmatrix}.       \tag{3}
\]

Extra A-environment coordinates are zero. All record Grams are forward Grams. For arbitrary original channels, retain their correct-output contractions and set K=G⊙H. With the target T having diagonal blocks I₂ and off-diagonal blocks J₂/2, let

\[
 F(A,B)={1\over4}\Lambda_2(T-K).
 \quad
 \delta(A,B)\ge {\operatorname{Tr}(T-K)_+\over4}\ge F(A,B). \tag{4}
\]

The first inequality includes the entire lost trace. Indeed the normalized maximally entangled logical/reference input has correct joint reference/output compression Kᵀ/8 on the orthonormal support {|f,i〉_R⊗|ff〉_out}; pinching gives
(‖K−T‖₁+8−Tr K)/8=Tr(T−K)₊/4. Thus no leakage calibration or physical channel transfer is being assumed.

A flat new-environment derivative has correct records r_fi=L_i b_fi and no wrong-output records, by section 85. An environment gauge removes the common L₀. Its remaining records are

\[
 r_{f0}=0,\qquad r_{f1}=D b_{f1},\qquad D=L_1-L_0.
 \quad E=\overline{D^*D}=r_0I_2+\sum_{a=1}^3r_a\sigma_a. \tag{5}
\]

The coefficients r_a are real. The conjugation in E fixes the convention relative to N_f in (1).

**Coefficient theorem.** Fix the records (5), denoting their full original-output Stinespring operator by R. Let U(s) be any smooth old rank-two comparison unitary, and V_A(s) any smooth original A-isometry, both based at the equality tuple. Consider the physical probability path

\[
 V_B(s)=U(s)\sqrt{I-sR^*R}\ \oplus\ \sqrt{s}\,R,
 \qquad s\ge0.                                          \tag{6}
\]

The coefficient q in F=1/4+s²q+o(s²) depends only on the first old comparison tangent. Its minimum over all such tangents, including arbitrary finite A-environments, original output leakage, and phase gauges, is

\[
 q_{\min}(D)=\sum_{a=1}^3c(u_a)r_a^2,
 \qquad c(u)={(1-u)(7u-1)^2\over256u^2}.                 \tag{7}
\]

The minimum is attained by a calibrated comparison tangent in A-environment dimension four. In particular

\[
 {35\over1024}|r|^2\le q_{\min}(D)\le {7\over144}|r|^2,
 \qquad q_{\min}(D)\ge {35\over2048}
       \|E-\tfrac12\operatorname{Tr}(E)I_2\|_F^2.        \tag{8}
\]

Both coefficient bounds are sharp over the classified disphenoids. If D has one row, then |r|²=‖D‖_F⁴/4, so q_min≥35‖D‖_F⁴/4096. A zero scalar component is not being assumed in (7).

**Amplitude-path consequence.** Suppose both original channels admit C² Stinespring paths V_A(t),V_B(t) in fixed finite environments through the equality pair. Split B into its base two-dimensional environment and its orthogonal complement. If the first new-environment derivative is flat, use (5) to define D. Then

\[
 \liminf_{t\downarrow0}{\delta(A(t),B(t))-1/4\over t^4}
       \ \ge\ \sum_{a=1}^3c(u_a)r_a^2.                  \tag{9}
\]

If that derivative is not flat, the liminf is +∞. It is also +∞ whenever the first old comparison tangent has a nonzero component normal to the section-86 minimum manifold. Equation (9) will be proved separately in section 87.7; it is not inferred merely from substituting s=t² into (6).

### 87.2. Comparison geometry and spectral expansion

We use the following proved section-86 facts, with their full original-channel scope. On
X=St(C⁸,C⁴⊗Cᵈ)×U(8), d≥4, the comparison function F is at least 1/4. Near (3) it has a smooth minimum manifold M with Hessian kernel exactly TM and positive definite normal Hessian. Its points are calibrated, balanced frames with

\[
 C_f=S+\tfrac12WN_f,\quad \sum_fN_f=0,\quad
 S^*S=(\tfrac12-h/8)I_2,\quad W^*W=(h/2)I_2,\quad
 S^*W=i\beta I_2.                                       \tag{10}
\]

Here h is near 1/2 and β near zero. The global fixed-A_m witness bound holds on this whole manifold, including its complex cross-bit marker overlaps. To verify it directly, put T_i=√2(S+(−1)^iW/2). Equations (10) give

\[
 T_i^*T_i=2\{S^*S+W^*W/4+(-1)^i(S^*W+W^*S)/2\}=I_2.
\]

Moreover a_fi=T_i conjugate(b_fi). Balance gives Σ_f|b_fi〉〈b_fi|=2I₂ separately for both fixed bits. Thus, writing H_i^m for this fixed-bit qubit Gram, one has H_i^m≤2I₄ and the corresponding A_m Gram is (H_i^m)ᵀ. Let H_i be the correct-output bit-i Gram of any original B, including arbitrary rank and output leakage. It is positive semidefinite and Tr H_i≤4. The fixed rank-two projection P₀=(J₄/4)⊗I₂ in bit coordinates sees only these same-bit sectors, so

\[
 \operatorname{Tr}(P_0K)=\tfrac14\sum_i\operatorname{Tr}(H_i^mH_i)
       \le\tfrac12\sum_i\operatorname{Tr}H_i\le4,
 \qquad \operatorname{Tr}(P_0T)=5.
\]

Ky Fan's variational inequality therefore gives F(A_m,B)≥Tr(P₀(T−K))/4≥1/4 for every original B. In particular every physical new-environment derivative at m is nonnegative. This argument does not require the cross-bit marker overlap to be real or equal to 3/4: the imaginary term S^*W=iβI₂ cancels in T_i^*T_i. Locally the section-86 normal Hessian result also gives F_old≥1/4+c dist(x,M)². These statements include the full plus/minus cross coupling and wrong-output blocks.

At the base the top two eigenvalues of T−K are 1/2,1/2. All others are at most zero, including on the disphenoid boundary. In plus/minus coordinates the top projection and reduced resolvent are

\[
 P=\operatorname{diag}(ss^*,ss^*),\quad s=\tfrac12(1,1,1,1)^T,
 \qquad
 \mathcal R=\operatorname{diag}\left(
 \sum_a{2P_a\over1+u_a},\ \sum_a{2P_a\over7u_a-1}\right),
 \quad P_a={\chi_a\chi_a^T\over4}.                       \tag{11}
\]

The gap is at least 1/2 uniformly. For K=K₀+sK₁+s²K₂+o(s²), spectral perturbation of the isolated cluster gives

\[
 F={1\over4}-{s\over4}\operatorname{Tr}(PK_1)
   +{s^2\over4}\operatorname{Tr}(-PK_2+PK_1\mathcal R K_1P)
   +o(s^2).                                             \tag{12}
\]

This formula keeps all cross blocks. Since dF_old=0 and the flat noise derivative is zero, no second old comparison derivative contributes to q.

The old calibrated tangent is described by C_f and N_f. Its dimension is 4(12+2)=56. There are a further eight independent bit-frame phase coordinates in B; changing A correspondingly leaves C,N unchanged. They lie in TM. Every mixed noise source vanishes on TM: the physical noise derivative is a nonnegative smooth function on M and is zero at the base for the flat R. Thus its differential there is zero. The eight phases are retained as zero directions, not removed by a change of the fixed target bit basis.

### 87.3. A complete Pauli-character formula

Here are explicit finite-dimensional formulas for the quadratic form being minimized. They also provide algebraic certificates for the parameter reduction below.

Put n=(x,y,z)=(n₁,n₂,n₃), σ₀=I₂, and fix the character χ₁. Write

\[
 \dot C_f={1\over4}\begin{bmatrix}\sqrt7 U_f\\V_f\end{bmatrix},
 \quad U_f=\chi_1(f)\sum_{\mu=0}^3\chi_\mu(f)u_\mu\sigma_\mu,
 \quad V_f=\chi_1(f)\sum_{\mu=0}^3\chi_\mu(f)v_\mu\sigma_\mu,
 \quad \dot N_f=\chi_1(f)\sum_{a=1}^3\chi_a(f)d_a\sigma_a. \tag{13}
\]

The coefficients u,v are complex and d real. The complete first-order constraints are

\[
 7\Re u_0+n\cdot\Re v=0,\qquad
 7\Re u+\Re v_0\,n-n\times\Im v=0,\qquad n\cdot d=0.  \tag{14}
\]

Take the following fourteen real coordinates, indexed from zero:

\[
 \xi=(\Im u_0,\Im u_x,\Im u_y,\Im u_z,
       \Re v_0,\Re v_x,\Re v_y,\Re v_z,
       \Im v_0,\Im v_x,\Im v_y,\Im v_z,d_x,d_y),          \tag{15}
\]

with d_z=−(xd_x+yd_y)/z and the real parts of u determined by (14). The same construction with χ₀,χ₂,χ₃ gives all four orthogonal fourteen-dimensional character blocks.

Set \dot D_f=\dot C_fN_f+C_f\dot N_f. Let K_ξ be the first variation of the full Gram of the eight matrix columns (C₁,…,C₄,C₁N₁,…,C₄N₄). Its old quadratic coefficient is ξᵀHξ, where H is defined explicitly by

\[
 \begin{split}
 \xi^TH\xi={}&{1\over4}\sum_f\|\dot C_f\|_F^2
 -{1\over32}\sum_f\Re\operatorname{Tr}(V_f^*\dot N_f)
 +{1\over32}\sum_f|\dot n_f|^2\\
 &-{1\over16}\left(\|\sum_f\dot C_f\|_F^2+
                         \|\sum_f\dot D_f\|_F^2\right)
 +{1\over4}\operatorname{Tr}(PK_\xi\mathcal R K_\xi P).
 \end{split}                                             \tag{16}
\]

Here \dot n_f is the Bloch vector of \dot N_f. This follows from (12) using normalized retractions with C_{2,f}=−C_f\dot C_f^*\dot C_f and N_{2,f}=−|\dot n_f|²N_f/2. In particular H is positive semidefinite because the comparison tuple is a minimum of F.

For completeness, the mixed source and fixed-noise term can be computed without choosing eigenvectors of N_f. Use bit coordinates in the rest of this paragraph, transforming P,ℛ,K_ξ by the fixed plus/minus Hadamard. Define

\[
 p_f=(I_2-N_f)/2,\quad e_{f0}=0,\quad e_{f1}=\operatorname{Tr}(p_fE),
 \quad J_{f1,g1}=\operatorname{Tr}(p_fp_gE),
 \quad J_{fi,gj}=0\text{ otherwise},
 \quad A_{\alpha\gamma}=(e_\alpha+e_\gamma)/2,
 \quad L=J-A\odot K_0,
 \quad Q_{\alpha\gamma}=-{(e_\alpha-e_\gamma)^2\over8}(K_0)_{\alpha\gamma}.
                                                               \tag{17}
\]

Thus L,Q are the first two noise-only Gram coefficients in (6). Put Y_f=[U_f;V_f], X_f=[I₂;N_f], and

\[
 M_f={1\over8}[7I_2\ {-I_2}]
       (Y_f+\tfrac12X_f\dot N_fN_f),\qquad
 J'_{f1,g1}=\operatorname{Tr}\{p_f(M_f^*+M_g)p_gE\},
 \qquad J'_{fi,gj}=0\text{ otherwise}.
\]

A horizontal lift of the qubit frame has \overline B_f'=\dot N_fN_f\overline B_f/2; substitution in A_f=√2C_f\overline B_f gives this M_f and J'. Consequently the mixed linear functional gᵀξ and noise constant q₀ are

\[
 g^T\xi={1\over4}\operatorname{Tr}\{P(A\odot K_\xi-J')
             +PK_\xi\mathcal R LP+PL\mathcal R K_\xi P\},
 \qquad q_0={1\over4}\operatorname{Tr}(-PQ+PL\mathcal R LP).
                                                               \tag{18}
\]

Equations (13)–(18) specify every matrix entry and every source component.

The Klein-four action combines the corresponding fibre permutation with Pauli conjugation. It preserves the base and (12), acts by χ_a on the Pauli coefficient r_a, and by χ₀ on r₀. Hence the old Hessian is block diagonal in the four character spaces, the σ_a source is in block a, and distinct noise characters have zero quadratic cross terms. Axes can therefore be permuted, so it suffices to compute E=σ₁ in block χ₁.

The scalar source and scalar noise constant are zero. One direct reason is as follows. Scalar E describes a common bit marker on B. At the base, its noise-only curve preserves the top projection P and its trace, so F=1/4. For A-variations, the scalar marker can be transferred algebraically to A's records; the section-81 rank-two contraction witness gives F≥1/4 for every original A. For U-variations at fixed A₀, the fixed-A₀ global best-response bound gives F≥1/4. Thus both parts of the mixed derivative vanish. Equivalently one may substitute E=I₂ in (17)–(18). The distinction between a fixed R and the varying marked U does not alter this mixed derivative: the noise derivative, as a nonnegative quadratic form in R with value zero at the flat base R, has zero first derivative in R there. Character orthogonality also removes all scalar–anisotropic quadratic cross terms.

### 87.4. Exact range certificate and minimization

The following algebraic reduction is useful; it is not a physical rotation of the equality disphenoid or a change of the target bit basis. Set ρ=√(1−x²), and form the auxiliary coefficients H_a,g_a by substituting (x,0,ρ) into (13)–(18). They are well-defined rational expressions even though this auxiliary point is outside the classified equality family. Apply

\[
 Q_x=\begin{bmatrix}1&0&0\\0&z/\rho&y/\rho\\0&-y/\rho&z/\rho\end{bmatrix}
\]

to each of the three-vector coordinate groups (Im u,Re v,Im v), leaving their scalar coordinates unchanged. On the two free d coordinates use d_x↦d_x and d_y↦−xy d_x/ρ²+z d_y/ρ. Denote this invertible fourteen-dimensional map by L_x. Direct substitution using σ_aσ_b=δ_abI+iε_abcσ_c and x²+y²+z²=1 gives

\[
 L_x^TH(x,y,z)L_x=H_a(x),\qquad L_x^Tg(x,y,z)=g_a(x).
                                                               \tag{19}
\]

This identity includes all fourteen rows and columns. In particular H_a is positive semidefinite by congruence with the physical H; no positivity assumption at an unphysical auxiliary frame is used.

Here is an explicit certificate for the remaining singular quadratic minimization. In the auxiliary coordinates let I=(2,7,12,4,10), namely (Im u_y,Re v_z,d_x,Re v₀,Im v_y), and put a=x². The source restricted to these coordinates, and the constant, are

\[
 g_I=\begin{bmatrix}
 -7\rho(4a-1)/(8(7a-1))\\
 -x\rho(4a^2-a+3)/(8(a+1)(7a-1))\\
 -3/(8(7a-1))\\ x/2\\ -\rho(a-1)/(4(a+1))
 \end{bmatrix},
 \qquad q_0=-{a(7a^2-26a+1)\over8(a+1)(7a-1)}.          \tag{20}
\]

The principal matrix H_I is block diagonal with blocks

\[
 \begin{bmatrix}
 {21a\over4(7a-1)}&{3x(a-1)\over4(7a-1)}&{-7\rho\over8(7a-1)}\\
 {3x(a-1)\over4(7a-1)}&{3a^3-3a^2+46a-4\over28(a+1)(7a-1)}&
 {-x\rho(a+5)\over8(a-1)(7a-1)}\\
 {-7\rho\over8(7a-1)}&{-x\rho(a+5)\over8(a-1)(7a-1)}&
 {-3\over4(a-1)(7a-1)}
 \end{bmatrix},
 \quad
 \begin{bmatrix}
 {15a-1\over7(7a-1)}&{x\rho\over7(7a-1)}\\
 {x\rho\over7(7a-1)}&{a(13a-1)\over7(a+1)(7a-1)}
 \end{bmatrix}.                                         \tag{21}
\]

Define the five-vector

\[
 z_I=\begin{bmatrix}
 -\rho(a+6)/14\\ x\rho/2\\ a-1\\
 (5a-1)(5a+1)/(16x^3)\\
 -\rho(17a^2-14a+1)/(16x^4)
 \end{bmatrix}.                                         \tag{22}
\]

Let z be its fourteen-dimensional extension by zero. Substituting (13)–(18) gives the full range identity, including every omitted and every gauge coordinate,

\[
 H_a z=g_a.                                              \tag{23}
\]

In particular this is stronger than checking only H_I z_I=g_I. All denominators in (19)–(23) are nonzero for 2/7≤a≤3/7 and for the original physical y,z>0. Equations (19) and (23) can also be checked purely by reducing numerators modulo ρ²−1+x² and z²−1+x²+y²; they are rational identities, not sampled numerical equalities.

Completion of squares is now valid despite the Hessian zero modes:

\[
 \xi^TH_a\xi+g_a^T\xi+q_0
   =(\xi+z/2)^TH_a(\xi+z/2)+q_0-g_I^Tz_I/4,
 \qquad
 q_0-g_I^Tz_I/4={(1-a)(7a-1)^2\over256a^2}.              \tag{24}
\]

The first term is nonnegative and vanishes at ξ=−z/2. Transport by L_x and permutation of the axes gives (7). Every minimizing tangent is an actual tangent of the smooth calibrated comparison manifold, so normalized local retractions realize it by a physical path (6).

For the sharp uniform bound, differentiation gives

\[
 c'(a)={-49a^3+15a-2\over256a^3}.
\]

The numerator is concave for a>0, and its values at 2/7 and 3/7 are 8/7 and 4/7. It is therefore positive throughout the interval. Thus c increases, with c(2/7)=35/1024 and c(3/7)=7/144. The endpoints occur in allowed disphenoids, proving (8) and sharpness.

### 87.5. No missing original-channel directions

We verify that the algebraic minimum is also the full original comparison-tangent minimum in (6).

First, the eight bit-frame phase directions and every other tangent to M have zero old Hessian and zero source, as proved in section 87.2. They cannot change (24).

Second, any extra A-environment direction orthogonal to the four-dimensional base support has zero source and zero Hessian cross term with the supported directions. The environment unitary which is the identity on the base support and minus the identity on its orthogonal complement fixes the base, the new B records, and F, but reverses precisely those tangent directions. Invariance forces those cross terms to vanish. Their own Hessian is nonnegative by the comparison minimum. This argument covers an arbitrary fixed finite A-environment.

Third, an original wrong-output tangent has no correct-output first derivative. The mixed source (18) is therefore zero for it: the new R in (5) is calibrated, R*R is fibre-block diagonal, and the correct blocks of U'R*R vanish for a pure wrong-output U' tangent. The exact section-86 leakage Hessian identity is

\[
 q_{\rm old,full}=q_{\rm old,calibrated}
                  +(\|L_A\|_F^2+\|L_B\|_F^2)/8.        \tag{25}
\]

Thus all leakage terms only add nonnegative cost. No relaxation of a physical Stinespring constraint is needed: every actual full tangent has the stated calibrated correct part and wrong-output part, while the minimizing calibrated tangent is itself realizable. These three observations establish the coefficient theorem with the complete original-channel scope claimed.

### 87.6. Exact scalar zero modes

Suppose D*D=λI₂. If λ>0, D/√λ is an isometry into the new environment. The following records give an exact calibrated physical path for small t:

\[
 b_{f0}(t)=b_{f0}\oplus0,\qquad
 b_{f1}(t)=\sqrt{1-\lambda t^2}\,b_{f1}\oplus tDb_{f1}.
                                                               \tag{26}
\]

This is a qubit core with bit-marker overlap q(t)=√(1−λt²). Choose the A records to be the same conjugate qubit core with normalized bit markers whose real overlap is

\[
 \eta_A(t)={3\over4q(t)}.                                \tag{27}
\]

This is feasible and smooth for sufficiently small t, including at t=0; for example choose marker coordinates (√((1+η_A)/2), (−1)^i√((1−η_A)/2)). Every same-bit product Gram is unchanged, and every cross-bit product overlap is multiplied by η_A(t)q(t)=3/4. Hence the entire product Gram K, and therefore the original calibrated logical product channel, is exactly the base one. Its full-reference error remains exactly 1/4. For λ>0 and t≠0 small the B environment span is four-dimensional, so these are genuine higher-rank quarter-attainers. The case λ=0 is trivial.

This explains the scalar zero in (7) by an actual physical family. It neither identifies all higher-order zero modes nor rules out higher-order anisotropic escape.

### 87.7. From the coefficient to arbitrary C² amplitude paths

We now prove (9), retaining the possibility of moving old tangents and higher new-environment derivatives. Write the actual B isometry in its fixed old/new split as V_B(t)=W(t)⊕R(t). Near zero W is square and has polar unitary U(t), so

\[
 V_B(t)=U(t)\sqrt{I-R(t)^*R(t)}\oplus R(t).
\]

The comparison point x(t)=(V_A(t),U(t)) is C². Choose smooth tubular coordinates near M, write its nearest point as m(t), and write its normal coordinate as n(t). These coordinates may be chosen in any fixed smooth local metric. The section-86 result gives a uniformly positive normal quadratic form and F_old=1/4 on M.

For arbitrary small R put D_R=R*R. The physical polar expansion through degree four in R is

\[
 \begin{split}
 B-B_U&=\Psi_{U,R}+\Theta_{U,R}+O(\|R\|_F^6),\\
 \Psi_{U,R}(Y)&=\operatorname{Tr}_{\rm new}(RYR^*)
                        -\tfrac12B_U(D_RY+YD_R),\\
 \Theta_{U,R}(Y)&=\tfrac14B_U(D_RYD_R)
                        -\tfrac18B_U(D_R^2Y+YD_R^2).
 \end{split}                                             \tag{28}
\]

The estimates hold in any fixed finite-dimensional channel norm, uniformly for U near the base. Let ℓ_x=d_BF at the old comparison channel. Smoothness of the isolated cluster gives

\[
 F_{\rm full}=F_{\rm old}+\ell_x\Psi_{U,R}
       +\ell_x\Theta_{U,R}
       +\tfrac12d_B^2F_x(\Psi_{U,R},\Psi_{U,R})
       +O(\|R\|_F^6).                                   \tag{29}
\]

For every m∈M and every R, the physical one-sided curve U_m√(I−sR*R)⊕√sR and the fixed-A_m best-response property imply the exact inequality

\[
 \ell_m\Psi_{U_m,R}\ge0.                               \tag{30}
\]

In normal coordinates, expand the middle term of (29) as

\[
 \ell_x\Psi_{U,R}=\ell_m\Psi_{U_m,R}
                  +\mathcal B_m(n,R)+O(\|n\|^2\|R\|_F^2),
                                                               \tag{31}
\]

where ℬ is linear in n and quadratic in R. This is an ordinary smooth Taylor expansion; its derivative includes both the change in ℓ and the change in U. Dropping the first term by (30) is crucial. It requires no Taylor expansion of R beyond its first derivative and introduces no possibly negative terms from R'' or from motion along M.

If n'(0)≠0, normal coercivity, (29)–(31), and R=O(t) give a strictly positive t² lower coefficient; the remaining possibly negative terms are O(t³)+O(t⁴). The liminf in (9) is then +∞. If R'(0) is not flat, the positive degree-two noise coefficient from section 85 gives the same conclusion (and the old normal quadratic coefficient is nonnegative).

It remains to consider n'(0)=0 and flat R₁=R'(0). A smooth environment rotation with first generator [[0,L₀*],[−L₀,0]] removes the common L₀ from R₁. It leaves the physical channels unchanged, keeps the paths C², and leaves the first old comparison derivative unchanged. We may therefore assume (5). Recompute the smooth split and normal coordinates after this rotation. Since they are C²,

\[
 n(t)=t^2n_2+o(t^2),\qquad R(t)=tR_1+o(t),\qquad m(t)\longrightarrow m_0.
                                                               \tag{32}
\]

Taylor expansion in normal coordinates gives F_old=1/4+q_{H,m}(n)+O(‖n‖³). Insert (32) into (29)–(31), drop (30), and use continuity of all coefficient forms. The result is

\[
 F_{\rm full}(t)\ge\tfrac14+t^4\{
       q_{H,0}(n_2)+\mathcal B_0(n_2,R_1)+q_{\rm noise,0}(R_1)
                         \}+o(t^4).                    \tag{33}
\]

The three terms in braces are exactly the old Hessian, mixed source, and fixed-noise constant calculated in (12)–(25). This identification follows either from (28)–(29) or by taking the probability path (6) with old tangent n₂. The tangent component along M has no effect because both Hessian and source vanish there. By (7) the braces are at least Σ_a c(u_a)r_a². Finally δ≥F from the full original pinching inequality (4) proves (9).

All estimates here are local about the chosen equality pair; the explicit coefficient bound (8) is uniform over the entire classified disphenoid region, but no uniform radius for the channel neighborhoods is asserted. Nonnegative fourth-order liminf does not imply a local minimum. Simultaneous arbitrary-channel approaches without these C² finite-amplitude lifts, and possible higher-order improvements in the remaining flat directions, are not settled by this theorem. The unrestricted quarter-optimum conjecture remains open.

The rank-at-most-three, path-free local Choi-tail bound continuing sections 86–87 is proved in [section 88 of the next continuation](ARITHMETIC_HOLOGRAPHIC_RT_III.md#88-a-path-free-local-quarter-minimum-for-a-party-of-kraus-rank-at-most-three).
