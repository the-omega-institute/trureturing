# Monotonicity with Finitely Many Exceptional Values

## Abstract

Continuity and nonnegative derivatives outside finitely many values imply interval monotonicity.

**Theorem 1.1 (Nonnegative derivatives away from exceptional values).**

$$\forall (f : \mathbb{R} \to \mathbb{R}), \forall (a : \mathbb{R}), \forall (b : \mathbb{R}), \forall (S : \operatorname{Set}(\mathbb{R})), (\operatorname{Finite}(S)) \Rightarrow (\operatorname{ContinuousOn}(f, \operatorname{Icc}(a, b))) \Rightarrow (\forall (t : \mathbb{R}), (t \in \operatorname{Ioo}(a, b)) \Rightarrow (\neg (\operatorname{f}(t) \in S)) \Rightarrow \exists (r : \mathbb{R}), \operatorname{HasDerivAt}(f, r, t) \land 0 \leq r) \Rightarrow \operatorname{MonotoneOn}(f, \operatorname{Icc}(a, b))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Monotonicity/FiniteExceptionalValuesMonotonicity.monotoneOn_Icc_of_hasDerivAt_nonneg_off_finite_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let f be a real-valued function continuous on the closed interval [a,b], and let S be a finite set of real values. At every interior point t for which f(t) is outside S, assume there is a real r such that HasDerivAt f r t and r is nonnegative. Then f is nondecreasing on [a,b]: whenever x and y belong to this interval and x is at most y, f(x) is at most f(y). The endpoints a and b are arbitrary; a reversed interval is empty, and a singleton interval also satisfies the conclusion.

The finiteness assumption concerns values, not domain points. The preimage of S can be infinite, and the derivative condition imposes no requirement there. For example, f(x) = max(0,x) on [-1,1] has S = {0} and preimage [-1,0]. It is continuous, has derivative 1 wherever its value is outside S, and is monotone, although it is not differentiable at zero. This illustrates the criterion without requiring a finite exceptional set of inputs.

Suppose instead that x is at most y but f(y) is strictly below f(x). Finiteness of S gives levels u and v strictly between f(y) and f(x), with u below v and with the entire open value interval (u,v) disjoint from S. The finite-set induction constructs such a gap by retaining a smaller interval on one side of each additional exceptional value.

Continuity and the intermediate value theorem make the level-u set in [x,y] nonempty. This level set is compact, so it has a first point c. Within [x,c], the level-v set is likewise nonempty and compact; let d be its last point. Then x is at most d, d is strictly below c, c is at most y, f(d) = v and f(c) = u. If an interior point of (d,c) had value at most u, the intermediate value theorem would give an earlier level-u crossing, contradicting the choice of c. If it had value at least v, it would give a later level-v crossing before c, contradicting the choice of d. Thus all interior values lie strictly in (u,v).

Every point of (d,c) is therefore an interior point of [a,b] whose value avoids S. Its nonnegative HasDerivAt witness gives differentiability and a nonnegative value of deriv. The mean-value monotonicity theorem, monotoneOn_of_deriv_nonneg, applies on [d,c] and yields f(d) at most f(c). This says v is at most u, contradicting the chosen gap. Equivalently, the descending secant would force a negative derivative by the mean value theorem.

Application to the native occurrence-weighted angle field. The original six positions are (12,13,14,34,24,23), and J(r,o,a,b)=(r,a,b,o,a,b). For a length quadruple q, put ℓ(q)_i=cosh(max((Jq)_i,0)). Extract θ(q) from the existing TwoLengthAngleSum.extendedAngle at slots (0,3,1,2), and set f(q)=(θ_r(q),θ_o(q),2θ_a(q),2θ_b(q)). The weights (1,1,2,2) retain both transverse occurrences. The corresponding TwoLengthAngleSum exposition gives the scalar map and the native local derivative calculation.

For any independent positive length quadruples p and q, define h=q−p and g(t)=h·f(p+th), 0≤t≤1. Every length coordinate on this segment remains positive. The native endpoint inequality obtained below is (q−p)·(f(q)−f(p))≥0 on the entire positive four-coordinate cone. The endpoints need not lie in the genuine formula domain.

Use the reduced scalar polynomials at z=cosh(p+th): d=r²+a²+b²+2rab−1, e=o²+a²+b²+2oab−1, L=(a+b)²−(r−1)(o−1), M=(r+1)(o+1)−(a−b)² and K=LM. Since each scalar coordinate is greater than 1, d,e>0. Also L+M=2(r+o+2ab)>0. If L and M are not both positive, then K≤0: otherwise their positive product and positive sum force both positive.

The original numerator identities give d²−N_r²=(r²−1)K, e²−N_o²=(o²−1)K, de−N_a²=(a²−1)K and de−N_b²=(b²−1)K. Therefore K≤0 forces the square of every normalized raw cosine to be at least 1. Such a real raw cosine is at least 1 or at most −1; after clamping, its angle is 0 or π. In particular, all four extracted angles of a nongenuine positive state belong to {0,π}.

For the fixed h, take S_h to be the set of h_r b_rπ+h_o b_oπ+2h_a b_aπ+2h_b b_bπ over the sixteen choices (b_r,b_o,b_a,b_b)∈{0,1}⁴. This set has at most sixteen values; some choices can give equal values. Every nongenuine point on the segment has g(t)∈S_h. No assertion about finiteness of the exceptional input points is needed, and no assertion that all sixteen angle patterns are realizable is made.

The function g is continuous on the whole closed segment. The four coordinate functions and their hyperbolic cosines are continuous, as are the scalar polynomial numerators and d,e. The axial denominators are d,e and the common transverse denominator is √(de); all remain positive along the segment. Division, minimum, maximum and arccos preserve continuity. The original six-frame identity identifies these continuous expressions with the existing extendedAngle, and the weighted sum gives the stated continuous g even where K=0.

At a point where g(t)∉S_h the state x=p+th is genuine: x>0, L(cosh x)>0 and M(cosh x)>0. Its native derivative is g′(t)=κ(x)Q(x,h), where κ=de/(K√K)>0. With u=θ(x), c_j=cos u_j and s_j=sin u_j, put P=s_a s_b, X=c_r+c_a c_b and Y=c_o+c_a c_b. The exact five-square formula is Q=(X²−P²)h_r²+(Y²−P²)h_o²+(s_rh_r+s_oh_o−2s_ac_bh_a−2s_bc_ah_b)²+(X−P)(Y−P)(h_a+h_b)²+(X+P)(Y+P)(h_a−h_b)².

The coefficient signs follow from the original length formulas. At z=cosh x, write v_a=sinh x_a and v_b=sinh x_b. Polynomial expansion gives eN_r+N_aN_b=K(o+ab) and dN_o+N_aN_b=K(r+ab). Together with the positive native sine branches, these yield X=K(o+ab)/(de), Y=K(r+ab)/(de) and P=K v_a v_b/(de).

Hence X±P=K[cosh x_o+cosh(x_a±x_b)]/(de), and Y±P=K[cosh x_r+cosh(x_a±x_b)]/(de), by the hyperbolic addition and subtraction identities. Each bracket is positive, so X−P, X+P, Y−P and Y+P are positive. In particular X²−P²=(X−P)(X+P)>0 and Y²−P²=(Y−P)(Y+P)>0. Every term of Q is nonnegative, proving the required nonnegative derivative at each interior point with value outside S_h.

The finite-exceptional-values criterion now applies directly to g on [0,1]. It gives g(0)≤g(1), and subtracting the endpoints yields ∑_{i=1}⁴(q_i−p_i)(f_i(q)−f_i(p))≥0. This is weak monotonicity of the actual occurrence-weighted formula on four independent positive length coordinates, including segments that meet nongenuine or flat states.

Extension to all real formula parameters. For arbitrary q∈ℝ⁴, each cosine-length coordinate ℓ(q)_i=cosh(max((Jq)_i,0)) is at least 1. If x,y,z≥1, then rad(x,y,z)=2xyz+x²+y²+z²−1≥4. The original square-root denominators are therefore strictly positive even at zero length. The six raw cosines, clamp and arccos, and hence the actual weighted field f, are continuous on all of ℝ⁴.

Own-coordinate vanishing. When q_i≤0, the cosine length at its corresponding original slot is 1. With that slot first in the frame, numerator(1,y,z,o,v,w)=(y+w)(z+v), while rad(1,y,w)=(y+w)² and rad(1,z,v)=(z+v)². Since y,z,v,w≥1, the two square roots are y+w and z+v; the raw cosine is 1 and the extended angle is 0. Thus f_i(q)=0 whenever q_i≤0. Every component of f is nonnegative because arccos takes values in [0,π] and the occurrence weights are positive.

The positive-cone inequality first reaches nonnegative endpoints by an actual limit. For p,q≥0, apply it to p+ε(1,1,1,1) and q+ε(1,1,1,1) for ε>0. Their displacement is exactly q−p. Continuity of the actual field as ε decreases to 0 gives (q−p)·(f(q)−f(p))≥0 on the closed nonnegative cone, with no derivative premise at a zero coordinate.

For arbitrary p,q∈ℝ⁴ let p⁺ and q⁺ be their coordinatewise maxima with zero. The definition of ℓ gives f(p⁺)=f(p) and f(q⁺)=f(q). Componentwise, (q_i⁺−p_i⁺)(f_i(q)−f_i(p))≤(q_i−p_i)(f_i(q)−f_i(p)). If both endpoint coordinates are nonnegative the terms agree. If both are nonpositive both field components vanish. If just q_i is nonpositive, the difference between right and left is −q_i f_i(p)≥0; if just p_i is nonpositive, that difference is −p_i f_i(q)≥0. Summing and applying the nonnegative-endpoint inequality proves the same weak field monotonicity for every pair p,q∈ℝ⁴.

Equivalently, for every p,h∈ℝ⁴, the real function t↦h·f(p+th) is nondecreasing on the whole real line. For s<t the endpoint inequality is (t−s)h·(f(p+th)−f(p+sh))≥0; dividing by t−s gives the claim. The case s=t is equality. Negative coordinates here are parameters of the specified positive-part extension, with the own-coordinate vanishing proved above.

This application proves monotonicity of the specified four-coordinate occurrence-weighted formula, including its extension to zero and negative parameters. It asserts no derivative at a flat point and no unrestricted six-independent-coordinate monotonicity theorem. A geometric interpretation of the formula values, one solution on the actual coupled global edge set, elimination of flat blocks, gluing and same-manifold realization remain separate mathematical obligations.

## References

- Truth anchor: `D5/S3/Analytic/Monotonicity/FiniteExceptionalValuesMonotonicity.monotoneOn_Icc_of_hasDerivAt_nonneg_off_finite_values`
