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
