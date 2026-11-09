# Left units and division

## Abstract

Nonzero left multiplication in a real Banach absolute-valued algebra.

**Theorem 1.1 (Every nonzero left multiplier is invertible).**

Lean statement: `D5/S3/Analytic/BanachGeometry/LeftUnitalAbsoluteValued.exists_left_multiplier_equiv`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BanachGeometry/LeftUnitalAbsoluteValued.exists_left_multiplier_equiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be a nonzero complete real normed vector space and m an arbitrary real bilinear multiplication on E. Suppose norm(m(x,y))=norm(x)norm(y) for every x,y, and m(e,y)=y for one e and every y. For every x not zero there exists a continuous real linear equivalence T whose value on each y is the same original product m(x,y). Its operator norm is norm(x), and its inverse operator norm is the reciprocal of norm(x). There is no associativity, right-unit, finite-dimensional, quadratic-norm or inner-product premise. Only x not zero is excluded; every y, including zero, remains in the original domain.

Exact norm multiplicativity makes each nonzero multiplier injective. In rank one, finite dimension follows from that rank and injectivity gives surjectivity. In rank greater than one the punctured real space is connected. Invertible multipliers form an open set, by continuity of the operator family and Mathlib's Neumann perturbation theorem. They also form a closed set within the punctured space: a multiplier within half the limiting nonzero vector's norm has inverse norm the reciprocal of its own vector norm, so the same perturbation theorem inverts the limiting multiplier. The original left unit supplies a member, and connectedness propagates invertibility to every nonzero vector. Mathlib homothety identities give both exact operator norms.

For OmegaQ020 Lemmas 3.1 and 3.2, start with the actual real vector space mathcal A, a real bilinear map m, and a seminorm p satisfying p(m(x,y))=p(x)p(y) for all original vectors. Put q(x)=p(x)^2 and N={x:p(x)=0}. The seminorm induces the topology used for this construction; no norm or topology on the original space is an extra premise. N is a real submodule, p(x+n)=p(x) for n in N, and multiplicativity gives m(x,n),m(n,x) in N. These are two-sided stability statements for the original bilinear operation; they do not presuppose a ring or associativity.

Take the literal submodule quotient Q=mathcal A/N and its projection pi(x)=[x]. Postcompose m with N.mkQ and apply LinearMap.liftQ₂ to the two copies of N. Its kernel obligations are exactly the two stability statements. The resulting real bilinear M satisfies M(pi(x),pi(y))=pi(m(x,y)). The canonical quotient norm equals p(x) on pi(x): its upper bound is Submodule.Quotient.norm_mk_le; for the reverse bound, norm_mk_lt supplies an arbitrarily close representative, whose p value agrees with p(x). Thus every pair u,v in Q satisfies norm(M(u,v))=norm(u)norm(v), including zeros.

A readable unit e means that p(m(e,x)-x)+p(m(x,e)-x)=0 for every original x. Each summand is nonnegative, so each difference belongs to N, and pi(e) is an exact left and right unit of M. If some p(x)>0, then pi(x) is nonzero; multiplying its norm by the unit shows norm(pi(e))=1. This norm-one conclusion requires the nonzero readout assumption. If p is identically zero, Q is the zero space; the quotient and extension constructions still apply, without a norm-one unit conclusion.

More generally, let E be any real normed vector space, possibly zero or incomplete, with any norm-multiplicative real bilinear m. Set B=UniformSpace.Completion E and let i=Completion.toComplₗᵢ be the canonical real linear isometry. LinearMap.mkContinuous₂ with bound one and ContinuousLinearMap.continuous₂ make m jointly continuous. Compose it with i and regard it as a double additive homomorphism into B. IsDenseInducing.extend_Z_bilin along the two actual completion inclusions gives a jointly continuous extension f, and extend_eq gives f(i(x),i(y))=i(m(x,y)). Completion.induction_on₃ transports both addition laws on their closed equality sets; induction_on₂ transports each real scalar law. LinearMap.mk₂ therefore packages f as a real bilinear map. The same two-variable closed-set argument transports exact norm multiplicativity and proves uniqueness among jointly continuous real bilinear extensions agreeing with m.

The closed equality f(i(e),z)=z transports an original left unit using Completion.induction_on. Independently, f(z,i(e))=z transports an original right unit. No unit or nontriviality is needed to construct the extension. For the original seminorm theory take E to be precisely Q above, with M as its multiplication. Then f(i(pi(x)),i(pi(y)))=i(pi(m(x,y))) and norm(i(pi(x)))^2=p(x)^2=q(x) for every original x,y. The same i is isometric and injective, so equalities between included quotient vectors pull back to Q, and squared-norm identities pull back to the original q through i composed with pi. Under nonzero readout and the readable unit, this completion supplies the nonzero Banach space and left unit for the theorem described here. Completion is a mathematical proof tool; original faithfulness F is neither used nor extended, and no new physical states are inferred.

On any completed carrier that already has these exact hypotheses, the preceding result supplies surjectivity for every nonzero left multiplier. The spectral-pencil application can then choose one complex coordinate for each x and nonzero y and use the same coordinate for every real alpha and beta, including zero coefficients and dependent pairs. Its independent-pair boundary forces a nonzero imaginary part, while the zero-combination branch is handled by the spectrum of the zero operator. The resulting parallelogram identity is on the original completed norm. The exact squared-norm parameter map into the pinned Frechet-von Neumann-Jordan constructor then supplies the compatible real inner-product structure on that carrier.

This conditional application does not construct the original seminorm quotient, descend its multiplication and readable unit, or pull the parallelogram identity back to the original p squared. Those obligations remain open, as do the full original Hopf, orientation, metric, connection and closed-loop clauses. The auxiliary complex space is not the original physical J.

The mathematical source attributes the absolute-valued algebra background to Rodriguez Palacios, One-sided division absolute valued algebras, Publicacions Matematiques 36(2B), 925-954. The result is a source formalization; no literature originality is claimed.

## References

- Truth anchor: `D5/S3/Analytic/BanachGeometry/LeftUnitalAbsoluteValued.exists_left_multiplier_equiv`
