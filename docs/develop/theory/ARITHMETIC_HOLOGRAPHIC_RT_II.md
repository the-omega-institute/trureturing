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
