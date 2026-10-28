# Necessary parameters on the actual interior prefix

## Abstract

The original chronological history supplies the primitive interior parameters.

Use the original cumulative endpoints A0=I and A(i+1)=T(wi)*Ai for arbitrary finite words w0,w1,w2. The positive oriented kernel condition states that its generator is nonzero rank one, its real span is exactly the kernel of the three prefix differences, and its determinant polar is strictly positive on every strictly positive rank-one source.

Primitive coordinates p=(a,b,c,d) have nonnegative integer entries, gcd(a,b)=gcd(c,d)=1 and ac+bd>0. Write f=(a,-b), ell=(c,-d), r=(d,c) and F(p)=f*ell. All four entries are nonzero exactly when a,b,c,d>0. StrictPhase(w,p,m) retains m0=0, Ai*f=f+mi*r at every original index, positivity at indices 1,2,3, and 1<=m1<m2<m3.

ParameterForm(w,p,m) retains a,b,c,d>0 and asserts the existence of integers x,n,sigma with x>d, gcd(x,d)=1, m1,n>=1, sigma in {+1,-1}, a=x-m1*d, b=m1*c-d, c=x+(n*(x+d)+sigma)*d and Q=1+nd>=2. It includes A1*f=(x,d), T(w1)=[[1,1],[Q,Q+sigma]], T(w2)=[[0,1],[1,n*(x+d)+sigma]], m2=m1+1, m3=m1+1+n*(x+d)+sigma and rank of the original prefix differences equal to three. The nonnegative integral unimodular first endpoint is the actual first word matrix, so that filter is retained.

ClassificationHypotheses(K,H,x,y,d,c,j,h) denotes all hypotheses in the following statement, including H*K!=2*K-I. MultiplierParameters(K,H,x,y,d,c,j,h,n,sigma) is the complete conjunction j=1, y=d, gcd(x,d)=1, n>=1, sigma=+1 or -1, h=n*(x+d)+sigma, c=x+hd, Q=1+nd>=2 and the two displayed exact matrix forms.

Forward realization as an application of the existing results.

For the converse choose integers x,d,m,n,sigma with d>=1, x>d, gcd(x,d)=1, m,n>=1 and sigma=+1 or -1. Set a=x-md>=1, h=n*(x+d)+sigma, c=x+hd, b=mc-d and Q=1+nd, and require gcd(a,b)=1. Choose any nonnegative integral first endpoint A1 of determinant +1 or -1 satisfying A1*(a,-b)=(x,d). Retain, independently, rank three for X mapping to (tr(A1*X)-tr(X),tr(K*A1*X)-tr(X),tr(H*K*A1*X)-tr(X)), with K=[[1,1],[Q,Q+sigma]] and H=[[0,1],[1,h]]. Neither first-endpoint admissibility nor this rank filter follows from the scalar parameters.

The inequalities give h>0, c>x>d, b>0 and Q>=2; gcd(c,d)=gcd(x,d)=1 and ac+bd=cx-d^2>0. Thus the natural casts of a,b,c,d form PrimitiveKernelLattice.PrimitiveCoordinates p with signed column f=(a,-b), signed row ell=(c,-d), direction r=(d,c) and matrix N=f*ell. These are the exact parameter identifications, with no rescaling or replacement of the first endpoint.

LegalMatrixMonoid.legal_matrix_monoid supplies a finite chronological native word uA for every such A1, with either determinant sign. For explicit next words, let lowerWord(q) repeat the chronological pair [J,M] q times. Since chronological concatenation reverses matrix multiplication, this pair has matrix L=M*J=[[1,0],[1,1]], while [M,J] has matrix U=J*M=[[1,1],[0,1]]. The pinned ModularGroup.coe_T_zpow gives the power formula for U; transpose, Matrix.transpose_pow and Matrix.map_pow give L^q=[[1,0],[q,1]]. The recursive lowerWord is the corresponding free-monoid power. LegalMatrixMonoid.product_append transports these powers to native products. The repository's private LegalMatrixMonoid.realize_word already implements the replacement of each Stern-Brocot L/U step by these same chronological J/M pairs; SternBrocot.UnimodularGeneration.unimodular_iff_wordMatrix supplies arbitrary determinant-one generation. The explicit shear powers use the pinned power formula rather than a new generation assertion.

Choose uK=[M,J]++lowerWord(Q) when sigma=+1, and uK=[J,M,J]++lowerWord(Q-1) when sigma=-1; choose uH=[J]++lowerWord(h). All exponents are nonnegative. Their matrices are respectively L^Q*U, L^(Q-1)*U*J and L^h*J, hence exactly K and H. Use the single word triple w=(uA,uK,uH), with cumulative endpoints I,A1,A2=K*A1,A3=H*K*A1. No inverse is executed and no acquisition is added.

The identity Q*(x+d)=c+(1-sigma)*d and direct multiplication give all four indexed equations jointly: A0*f=f, A1*f=(x,d)=f+m*r, A2*f=(x+d,c+d)=f+(m+1)*r and A3*f=(c+d,d+(h+1)*c)=f+(m+1+h)*r. Set the integer index vector to (0,m,m+1,m+1+h). LegalMatrixMonoid.product_append identifies the cumulative endpoints, so the retained endpoint rank filter is exactly rank(prefixDifference w)=3. Apply the converse projection PrimitiveKernelLattice.whole_class_primitive_lattice.2 to this same w,p and index vector. It gives N nonzero of rank one, the entire kernel equal to its real line, and strictly positive determinant polar on every strictly positive rank-one S. Concretely that polar is bd*S00+bc*S01+ad*S10+ac*S11>0. The same identifications assemble ParameterForm(w,p,(0,m,m+1,m+1+h)); no extra mathematical bridge is needed.

Actual positive sources remain independent of the auxiliary signed kernel vectors. For every strictly positive rank-one real matrix S, det(S)=0, so S satisfies TraceFibers.FixedFiberPairModulus.positiveSource. The universal factorization component of its result gives positive columns fplus and rows ellplus with S=vecMulVec(fplus,ellplus) and tr(B*S)=ellplus dot (B*fplus) for every real matrix B. One exact available instantiation is upper=true, executed=[advance,exchange], continuation=[advance], k=1, x=1, zeta=1 and tau=0, followed by the fourth conjunction projection; its auxiliary execution parameters impose no restriction on the universally quantified S or B. PhaseRigidity.positive_sum gives positivity of T(u)*fplus for every finite native word u, including every unread prefix of this same execution. The row ellplus stays fixed. For every real gain slope k, whole constant drift delta and original index i=0,1,2,3, (1+i*k)*(ellplus dot (Ai*fplus))+delta=(1+i*k)*tr(Ai*S)+delta. Negative slopes and erased gains are included.

Together with the necessity result below, these applications give the necessity and sufficiency derivation with both determinant signs and the original first-endpoint and rank filters. The conjugate correspondence uses the same four indices and restores the negative branch. This application introduces no separate mathematical declaration. It asserts neither positive multiplicity nor global recovery, a classification of all first endpoints, a final-word rank classification, sharper read bounds, resource bounds or physical acquisition costs.

**Theorem 1.1 (The two multipliers and the divisibility parameter).**

$$\forall K,H,x,y,d,c,j,h, \operatorname{ClassificationHypotheses}(K, H, x, y, d, c, j, h)\implies \exists n,sigma\in \mathbb{Z}, \operatorname{MultiplierParameters}(K, H, x, y, d, c, j, h, n, sigma)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/InteriorPrefixClassification.two_transition_parameters` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive primitive v=(x,y), r=(d,c), t=xc-yd>0 and x>d, retain two consecutive legal actions Kv=v+jr, H(v+jr)=v+(j+h)r with j,h>=1. Exclude H*K=2*K-I. Then j=1, y=d and there exist n>=1 and sigma=+1 or -1 with h=n*(x+d)+sigma, c=x+hd, Q=1+nd>=2, K=[[1,1],[Q,Q+sigma]] and H=[[0,1],[1,h]].

Last-transition rigidity gives H and y=d. The first coordinate equation and integer nonnegativity force the first row of K to be (1,1). Its determinant sets the lower-right entry to Q+sigma. If Q=1 and sigma=-1, c>x fails. If Q=1 and sigma=1, h=1 and H*K=2*K-I, the excluded relation. Coprimality of x,d now gives d dividing Q-1 and hence n>=1. This explicit exclusion is a hypothesis of this intermediate result; the next result derives it from the original rank condition.

OriginalCoordinates(w,N,p,s,m) means s>0, N=s*F(p), m0=0 and all four original lattice equations. ConjugateCoordinates means every unchanged-index endpoint identity and J*N*J=s*F(b,a,d,c). FirstEndpointFilters(w) means that its actual first endpoint has nonnegative integer entries and determinant +1 or -1. Both w and its literal conjugate satisfy that filter. The two ParameterForm alternatives below have exactly the full definition in the preceding paragraph, including the original rank-three test.

**Theorem 1.2 (Every interior history has the required parameter form).**

$$\forall w,N, \operatorname{OrientedKernelGenerator}(w, N)\land \operatorname{AllEntriesNonzero}(N)\implies \exists p,s,m, \operatorname{OriginalCoordinates}(w, N, p, s, m)\land \operatorname{ConjugateCoordinates}(w, N, p, s, m)\land \operatorname{FirstEndpointFilters}(w)\land \operatorname{FirstEndpointFilters}(\operatorname{conjugateHistory}(w))\land(\operatorname{ParameterForm}(w, p, m)\lor \operatorname{ParameterForm}(\operatorname{conjugateHistory}(w), \operatorname{swapCoordinates}(p), -m))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/InteriorPrefixClassification.interior_necessity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original word triple w and every arbitrary real positive oriented generator N with four nonzero entries, there exist primitive p, a positive real scale s and integer parameters m on the original four indices. They satisfy N=s*F(p), m0=0 and every original lattice equation. All conjugate endpoints satisfy Aprime_i=J*Ai*J and J*N*J=s*F(b,a,d,c). Either ParameterForm(w,p,m) holds or ParameterForm(wprime,(b,a,d,c),-m) holds.

The frozen phase theorem supplies exactly these two branches. In either strict positive branch the actual second and third words give the two transitions. Rank three makes the prefix difference map surjective. A relation H*K=2*K-I would imply A3=2*A2-A1, hence the third difference equals twice the second minus the first, contradicting surjectivity. The integer transition classification therefore applies without adding a hypothesis to the original prefix.

The conjugate words are [J]++wi++[J], so an empty multiplier becomes [J,J]. Matrix identity is kept distinct from literal emptiness. The signed column becomes -J*f, the signed row becomes -ell*J, and the parameters become -mi. Original read indices are unchanged. These signed vectors specify the auxiliary kernel; they are not positive physical sources.

## References

- Truth anchor: `D5/S3/Observer/CubicGain/InteriorPrefixClassification.interior_necessity`
- Truth anchor: `D5/S3/Observer/CubicGain/InteriorPrefixClassification.two_transition_parameters`
- Dependency: [D5/S3/Observer/CubicGain/InteriorNormalForm](InteriorNormalForm.md)
