# Necessary parameters on the actual interior prefix

## Abstract

The original chronological history supplies the primitive interior parameters.

Use the original cumulative endpoints A0=I and A(i+1)=T(wi)*Ai for arbitrary finite words w0,w1,w2. The positive oriented kernel condition states that its generator is nonzero rank one, its real span is exactly the kernel of the three prefix differences, and its determinant polar is strictly positive on every strictly positive rank-one source.

Primitive coordinates p=(a,b,c,d) have nonnegative integer entries, gcd(a,b)=gcd(c,d)=1 and ac+bd>0. Write f=(a,-b), ell=(c,-d), r=(d,c) and F(p)=f*ell. All four entries are nonzero exactly when a,b,c,d>0. StrictPhase(w,p,m) retains m0=0, Ai*f=f+mi*r at every original index, positivity at indices 1,2,3, and 1<=m1<m2<m3.

ParameterForm(w,p,m) retains a,b,c,d>0 and asserts the existence of integers x,n,sigma with x>d, gcd(x,d)=1, m1,n>=1, sigma in {+1,-1}, a=x-m1*d, b=m1*c-d, c=x+(n*(x+d)+sigma)*d and Q=1+nd>=2. It includes A1*f=(x,d), T(w1)=[[1,1],[Q,Q+sigma]], T(w2)=[[0,1],[1,n*(x+d)+sigma]], m2=m1+1, m3=m1+1+n*(x+d)+sigma and rank of the original prefix differences equal to three. The nonnegative integral unimodular first endpoint is the actual first word matrix, so that filter is retained.

ClassificationHypotheses(K,H,x,y,d,c,j,h) denotes all hypotheses in the following statement, including H*K!=2*K-I. MultiplierParameters(K,H,x,y,d,c,j,h,n,sigma) is the complete conjunction j=1, y=d, gcd(x,d)=1, n>=1, sigma=+1 or -1, h=n*(x+d)+sigma, c=x+hd, Q=1+nd>=2 and the two displayed exact matrix forms.

**Theorem 1.1 (The two multipliers and the divisibility parameter).**

$$\forall K,H,x,y,d,c,j,h, \operatorname{ClassificationHypotheses}(KHxydcjh)\implies \exists n,sigma\in \mathbb{Z}, \operatorname{MultiplierParameters}(KHxydcjhnsigma)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/InteriorPrefixClassification.two_transition_parameters` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive primitive v=(x,y), r=(d,c), t=xc-yd>0 and x>d, retain two consecutive legal actions Kv=v+jr, H(v+jr)=v+(j+h)r with j,h>=1. Exclude H*K=2*K-I. Then j=1, y=d and there exist n>=1 and sigma=+1 or -1 with h=n*(x+d)+sigma, c=x+hd, Q=1+nd>=2, K=[[1,1],[Q,Q+sigma]] and H=[[0,1],[1,h]].

Last-transition rigidity gives H and y=d. The first coordinate equation and integer nonnegativity force the first row of K to be (1,1). Its determinant sets the lower-right entry to Q+sigma. If Q=1 and sigma=-1, c>x fails. If Q=1 and sigma=1, h=1 and H*K=2*K-I, the excluded relation. Coprimality of x,d now gives d dividing Q-1 and hence n>=1. This explicit exclusion is a hypothesis of this intermediate result; the next result derives it from the original rank condition.

OriginalCoordinates(w,N,p,s,m) means s>0, N=s*F(p), m0=0 and all four original lattice equations. ConjugateCoordinates means every unchanged-index endpoint identity and J*N*J=s*F(b,a,d,c). FirstEndpointFilters(w) means that its actual first endpoint has nonnegative integer entries and determinant +1 or -1. Both w and its literal conjugate satisfy that filter. The two ParameterForm alternatives below have exactly the full definition in the preceding paragraph, including the original rank-three test.

**Theorem 1.2 (Every interior history has the required parameter form).**

$$\forall w,N, \operatorname{OrientedKernelGenerator}(wN)\land \operatorname{AllEntriesNonzero}(N)\implies \exists p,s,m, \operatorname{OriginalCoordinates}(wNpsm)\land \operatorname{ConjugateCoordinates}(wNpsm)\land \operatorname{FirstEndpointFilters}(w)\land \operatorname{FirstEndpointFilters}(\operatorname{conjugateHistory}(w))\land(\operatorname{ParameterForm}(wpm)\lor \operatorname{ParameterForm}(\operatorname{conjugateHistory}(w)\operatorname{swapCoordinates}(p)-m))$$

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
