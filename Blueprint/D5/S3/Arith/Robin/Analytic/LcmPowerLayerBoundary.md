# Uniform LCM power layer boundaries

## Abstract

The LCM power layer comparison above an explicit threshold independent of the layer index.

**Theorem 1.1 (An explicit threshold for all layers).**

$$\forall kappa \in \mathbb{R},\; (1 < kappa) \Rightarrow (\forall x \in \mathbb{R},\; (\operatorname{exp}\left(\operatorname{max}\left(6, ((2)^{kappa + \frac{101}{100}})^{\frac{1}{kappa - 1}}\right)\right) \le x) \Rightarrow (\forall ell \in \mathbb{N},\; (2 \le ell) \Rightarrow (\operatorname{lcmPowerF}\left(kappa, x, 1\right) < \operatorname{lcmPowerF}\left(kappa, (x)^{\frac{1}{ell}}, ell\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/LcmPowerLayerBoundary.layer_boundary_explicit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Steve Fan, Mits Kobayashi, Grant Molnar (2025). *A family of analogues to the Robin criterion*. DOI: [10.1007/s11139-026-01408-3](https://doi.org/10.1007/s11139-026-01408-3). URL: <https://arxiv.org/abs/2511.02106v1>.

*Commentary.*

For every real kappa>1, put u=max(6,(2^(kappa+1.01))^(1/(kappa-1))). For every real x>=exp(u) and every natural ell>=2, F(kappa,x,1)<F(kappa,x^(1/ell),ell). The function F is the real-valued expression in Definition 4.2 of Fan, Kobayashi and Molnar, A family of analogues to the Robin criterion. The threshold depends on kappa alone and is not claimed to be optimal.

Put B(s)=log((1+s)^kappa-s^kappa) and phi(s)=s*B'(s). The logarithmic power difference is concave, its derivative decreases on the positive half-line, and phi strictly increases there. For u=log(x), let v=2/u and r=2/(u+2). The elasticity formula gives phi(v)>=kappa*(r-r^kappa). The threshold implies u>=6 and u^(kappa-1)>=2^(kappa+1.01)>2*2^kappa. Hence u*r>=3/2 and u*r^kappa<=2^kappa/u^(kappa-1)<1/2, so u*phi(2/u)>kappa. If n>=2 and 0<s<=n/u, decrease of B' and increase of phi give n*B'(s)>=u*phi(n/u)>=u*phi(2/u)>kappa.

Set y=x^(1/ell), h=y^(-ell), and s=(1-h)/(y-1). The logarithm bound log(y)<=y-1 gives s<=ell/u. Factoring F gives kappa*log(y)*F(kappa,y,ell)=B(s)-B(s-h) and kappa*ell*log(y)*F(kappa,y^ell,1)=B(h). Concavity gives B(s)-B(s-h)>=h*B'(s), whereas B(h)<kappa*h. The explicit derivative bound yields ell*(B(s)-B(s-h))>B(h), which is the required strict comparison.

**Theorem 1.2 (A threshold independent of the layer).**

$$\forall kappa \in \mathbb{R},\; (1 < kappa) \Rightarrow (\exists X \in \mathbb{R},\; \forall x \in \mathbb{R},\; (X \le x) \Rightarrow (\forall ell \in \mathbb{N},\; (2 \le ell) \Rightarrow (\forall xell \in \mathbb{R},\; (1 < xell) \Rightarrow ((\operatorname{lcmPowerF}\left(kappa, xell, ell\right) = \operatorname{lcmPowerF}\left(kappa, x, 1\right)) \Rightarrow ((x)^{\frac{1}{ell}} < xell)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/LcmPowerLayerBoundary.layer_boundary_uniform` (`✓ std3`). ∎

*Resolves.* `Problems/fan-kobayashi-molnar-2026-remark-5-5` (proved) by `D5/S3/Arith/Robin/Analytic/LcmPowerLayerBoundary.layer_boundary_uniform`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"fan-kobayashi-molnar-2026-remark-5-5","declaration_gid":"D5/S3/Arith/Robin/Analytic/LcmPowerLayerBoundary.layer_boundary_uniform","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Steve Fan, Mits Kobayashi, Grant Molnar (2025). *A family of analogues to the Robin criterion*. DOI: [10.1007/s11139-026-01408-3](https://doi.org/10.1007/s11139-026-01408-3). URL: <https://arxiv.org/abs/2511.02106v1>.

*Commentary.*

For every real kappa>1 there is a real threshold X such that for every real x>=X, every natural ell>=2 and every real xell>1, F(kappa,xell,ell)=F(kappa,x,1) implies x^(1/ell)<xell. This follows from the explicit layer-base comparison by choosing X=exp(max(6,(2^(kappa+1.01))^(1/(kappa-1)))). This is the single settlement result, in the literal layer-base form of Remark 5.5.

**Theorem 1.3 (Strict decrease in the base).**

$$\forall kappa \in \mathbb{R},\; (1 < kappa) \Rightarrow (\forall ell \in \mathbb{N},\; (1 \le ell) \Rightarrow (\forall x \in \mathbb{R},\; \forall y \in \mathbb{R},\; (1 < x) \Rightarrow ((1 < y) \Rightarrow ((x < y) \Rightarrow (\operatorname{lcmPowerF}\left(kappa, y, ell\right) < \operatorname{lcmPowerF}\left(kappa, x, ell\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/LcmPowerLayerBoundary.F_strictAntiOn` (`✓ std3`). ∎

*Citation.* Steve Fan, Mits Kobayashi, Grant Molnar (2025). *A family of analogues to the Robin criterion*. DOI: [10.1007/s11139-026-01408-3](https://doi.org/10.1007/s11139-026-01408-3). URL: <https://arxiv.org/abs/2511.02106v1>.

*Commentary.*

For every kappa>1 and every natural ell>=1, F(kappa,.,ell) strictly decreases on (1,infinity). This statement is the natural-layer restriction of source Theorem 4.3. The repository gives an independent proof that does not use that theorem. For t>0 write S(n,t)=t+...+t^n and D(n,t)=dS(n,t)/dt. Termwise comparison gives t*D(n,t)<=n*S(n,t), which implies D(n,t)/S(n,t)<=D(n+1,t)/S(n+1,t) for n>=1. Together with strict increase of phi and positivity of B', this makes B(S(n+1,t))-B(S(n,t)) strictly increasing and positive. The case n=0 follows directly from B'>0 and B(0)=0. Substituting t=1/y makes the numerator of F strictly decrease, while its positive denominator kappa*log(y) increases.

**Theorem 1.4 (Comparison of equal-value layer bases).**

$$\forall kappa \in \mathbb{R},\; (1 < kappa) \Rightarrow (\forall x \in \mathbb{R},\; \forall xell \in \mathbb{R},\; (\operatorname{exp}\left(\operatorname{max}\left(6, ((2)^{kappa + \frac{101}{100}})^{\frac{1}{kappa - 1}}\right)\right) \le x) \Rightarrow (\forall ell \in \mathbb{N},\; (2 \le ell) \Rightarrow ((1 < xell) \Rightarrow ((\operatorname{lcmPowerF}\left(kappa, xell, ell\right) = \operatorname{lcmPowerF}\left(kappa, x, 1\right)) \Rightarrow ((x)^{\frac{1}{ell}} < xell)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/LcmPowerLayerBoundary.layer_boundary_xl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Steve Fan, Mits Kobayashi, Grant Molnar (2025). *A family of analogues to the Robin criterion*. DOI: [10.1007/s11139-026-01408-3](https://doi.org/10.1007/s11139-026-01408-3). URL: <https://arxiv.org/abs/2511.02106v1>.

*Commentary.*

Above the same explicit threshold, if xell>1 and F(kappa,xell,ell)=F(kappa,x,1), then xell>x^(1/ell). The explicit comparison and the strict decrease just proved give this conclusion without constructing an inverse function or assuming existence of a layer base. Thus the conclusion applies whenever the source layer variables satisfy their defining equality.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerLayerBoundary.F_strictAntiOn`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerLayerBoundary.layer_boundary_explicit`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerLayerBoundary.layer_boundary_uniform`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/LcmPowerLayerBoundary.layer_boundary_xl`
- Dependency: [D5/S3/Arith/Robin/Analytic/LcmPowerLemmaFifteen](LcmPowerLemmaFifteen.md)
