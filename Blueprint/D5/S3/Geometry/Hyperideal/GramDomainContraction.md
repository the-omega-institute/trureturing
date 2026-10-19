# Contracting the actual six-coordinate Gram domain

## Abstract

The full six-cosh negative-determinant Gram domain has an explicit contraction.

Use the edge order (12,13,14,34,24,23). For x in R6, G(x) is the existing OriginalCosineDeterminantInterface.gram: its diagonal is one and its six off-diagonal edge entries are minus the corresponding coordinates of x. Write Delta(x)=-det(G(x)). X is the subtype of R6 defined by x_i>1 for every i and Delta(x)>0, with its inherited Euclidean topology. The center is the vector with every coordinate equal to two.

**Theorem 1.1 (The entire parameter domain is contractible).**

$$ContractibleSpace\left(X\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/GramDomainContraction.full_domain_contractible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative offsets (a,b,c,d,e,f), the negative determinant Delta(x(s)), for x(s)=1+s*(a,b,c,d,e,f), is 16+c1*s+c2*s^2+c3*s^3+c4*s^4. Put p=a+d, q=b+e, r=c+f, U=a*d, V=b*e, W=c*f and T=a*b*f+a*c*e+b*c*d+d*e*f. The coefficients are c1=8*(p+q+r), c2=4*(p*q+p*r+q*r), c3=2*(T+p*(V+W-U)+q*(U+W-V)+r*(U+V-W)), and c4=2*(U*V+U*W+V*W)-U^2-V^2-W^2.

The first two coefficients are nonnegative. When c4 is nonnegative, choose a largest opposite-pair product, say U. The quartic inequality yields U-V-W<=2*sqrt(V*W), while AM-GM gives T>=2*p*sqrt(V*W). The other two terms in c3 are nonnegative, so c3 is nonnegative. All terms beyond the constant are then nonnegative for s>=0. When c4 is nonpositive and 0<=s<=1, comparison with 16*(1-s^3)+s^3*Delta(x(1)) gives the same endpoint bound. Thus Delta(1+s*(x-1)) is at least min(16,Delta(x)) throughout 0<=s<=1.

For x in X set M(x)=max(1,x0-1,...,x5-1) and eta(x)=1/M(x). The first homotopy moves x to 1+eta(x)*(x-1) along the preceding radial segment, with scale 1-t*(1-eta(x)). Its scale stays strictly positive, so every coordinate remains greater than one; the determinant bound keeps it in X.

The compressed offsets lie in (0,1]. The second homotopy linearly moves these offsets to the all-one vector. On the entire closed offset cube [0,1]^6, the cubic coefficient is at least -12 and the quartic coefficient at least -3. Hence Delta is at least 16-12-3=1 there. Every point of the second homotopy therefore lies in X. Both homotopies are continuous jointly in time and x, and their concatenation runs from the identity to the constant map at the center.

The domain includes every six-coordinate point satisfying its two defining conditions. To use this contraction for angle Jacobians, one must also identify the actual cosine domain and verify the derivative and matrix hypotheses on that same domain.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/GramDomainContraction.full_domain_contractible`
- Dependency: [D5/S3/Geometry/Hyperideal/OriginalCosineDeterminantInterface](OriginalCosineDeterminantInterface.md)
