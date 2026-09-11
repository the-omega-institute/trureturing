# Degree-Three Gribinski Discriminant

## Abstract

The denominator-cleared cubic discriminant is nonnegative for all nonnegative ordered-gap coordinates and every nonnegative parameter t.

**Definition 1.1 (Denominator-Cleared Discriminant).**

Lean statement: `D5/S3/Zeros/Convolution/GribinskiDegreeThreeDiscriminant.numerator`

*Formalization.* `D5/S3/Zeros/Convolution/GribinskiDegreeThreeDiscriminant.numerator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real t,s,a,b,c,d, N(t,s,a,b,c,d) denotes numerator t s a b c d. It is s^2*(a+b*t)^2*(6+3*t)-4*(a+b*t)^3 -4*s^3*(c+d*t)*(6+3*t)^2-27*(c+d*t)^2*(6+3*t) +18*s*(a+b*t)*(c+d*t)*(6+3*t).

**Theorem 1.2 (Nonnegativity on Ordered Gap Coordinates).**

$$\forall t,x,u,v,y,w,z\in\mathbb{R}, (0\le t \land 0\le x \land 0\le u \land 0\le v \land 0\le y \land 0\le w \land 0\le z) \implies 0\le \operatorname{N}\left(t, x+(x+u)+(x+u+v)+y+(y+w)+(y+w+z), 6\cdot(x\cdot(x+u)+x\cdot(x+u+v)+(x+u)\cdot(x+u+v)+y\cdot(y+w)+y\cdot(y+w+z)+(y+w)\cdot(y+w+z))+2\cdot(x+(x+u)+(x+u+v))\cdot(y+(y+w)+(y+w+z)), 3\cdot(x\cdot(x+u)+x\cdot(x+u+v)+(x+u)\cdot(x+u+v)+y\cdot(y+w)+y\cdot(y+w+z)+(y+w)\cdot(y+w+z))+2\cdot(x+(x+u)+(x+u+v))\cdot(y+(y+w)+(y+w+z)), 6\cdot(x\cdot(x+u)\cdot(x+u+v)+y\cdot(y+w)\cdot(y+w+z)), 3\cdot(x\cdot(x+u)\cdot(x+u+v)+y\cdot(y+w)\cdot(y+w+z))+(x+(x+u)+(x+u+v))\cdot(y\cdot(y+w)+y\cdot(y+w+z)+(y+w)\cdot(y+w+z))+(x\cdot(x+u)+x\cdot(x+u+v)+(x+u)\cdot(x+u+v))\cdot(y+(y+w)+(y+w+z))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Convolution/GribinskiDegreeThreeDiscriminant.ordered_numerator_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real t,x,u,v,y,w,z with 0<=t, 0<=x, 0<=u, 0<=v, 0<=y, 0<=w and 0<=z, let A1=x+(x+u)+(x+u+v), A2=x*(x+u)+x*(x+u+v)+(x+u)*(x+u+v), A3=x*(x+u)*(x+u+v), B1=y+(y+w)+(y+w+z), B2=y*(y+w)+y*(y+w+z)+(y+w)*(y+w+z), and B3=y*(y+w)*(y+w+z). The conclusion is 0<=N(t,A1+B1,6*(A2+B2)+2*A1*B1,3*(A2+B2)+2*A1*B1, 6*(A3+B3),3*(A3+B3)+A1*B2+A2*B1). The displayed formula expands all six local definitions. The domain includes t=0 and zero gaps.

## References

- Truth anchor: `D5/S3/Zeros/Convolution/GribinskiDegreeThreeDiscriminant.numerator`
- Truth anchor: `D5/S3/Zeros/Convolution/GribinskiDegreeThreeDiscriminant.ordered_numerator_nonneg`
