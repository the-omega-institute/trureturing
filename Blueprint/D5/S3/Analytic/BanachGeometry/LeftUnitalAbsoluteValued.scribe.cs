using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.BanachGeometry;

internal sealed class LeftUnitalAbsoluteValuedDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonzero left multiplication in a real Banach absolute-valued algebra.",
        H("Left units and division"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("left-unital-absolute-valued-multiplier"),
                DeclarationHandle.Create("D5/S3/Analytic/BanachGeometry/LeftUnitalAbsoluteValued.exists_left_multiplier_equiv"),
                H("Every nonzero left multiplier is invertible"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let E be a nonzero complete real normed vector space and m an arbitrary "
                        + "real bilinear multiplication on E. Suppose norm(m(x,y))=norm(x)norm(y) "
                        + "for every x,y, and m(e,y)=y for one e and every y. For every x not zero "
                        + "there exists a continuous real linear equivalence T whose value on "
                        + "each y is the same original product m(x,y). Its operator norm is norm(x), "
                        + "and its inverse operator norm is the reciprocal of norm(x). "
                        + "There is no associativity, right-unit, finite-dimensional, quadratic-norm "
                        + "or inner-product premise. Only x not zero is excluded; every y, "
                        + "including zero, remains in the original domain.")),
                    Paragraph(Text(
                        "Exact norm multiplicativity makes each nonzero multiplier injective. "
                        + "In rank one, finite dimension follows from that rank and injectivity "
                        + "gives surjectivity. In rank greater than one the punctured real space "
                        + "is connected. Invertible multipliers form an open set, by continuity "
                        + "of the operator family and Mathlib's Neumann perturbation theorem. "
                        + "They also form a closed set within the punctured space: a multiplier "
                        + "within half the limiting nonzero vector's norm has inverse norm "
                        + "the reciprocal of its own vector norm, so the same perturbation "
                        + "theorem inverts the limiting multiplier. The original left unit "
                        + "supplies a member, and connectedness propagates invertibility "
                        + "to every nonzero vector. Mathlib homothety identities give both "
                        + "exact operator norms.")),
                    Paragraph(Text(
                        "For OmegaQ020 Lemmas 3.1 and 3.2, start with the actual real vector "
                        + "space mathcal A, a real bilinear map m, and a seminorm p satisfying "
                        + "p(m(x,y))=p(x)p(y) for all original vectors. Put q(x)=p(x)^2 and "
                        + "N={x:p(x)=0}. The seminorm induces the topology used for this "
                        + "construction; no norm or topology on the original space is an extra "
                        + "premise. N is a real submodule, p(x+n)=p(x) for n in N, and "
                        + "multiplicativity gives m(x,n),m(n,x) in N. These are two-sided "
                        + "stability statements for the original bilinear operation; they do "
                        + "not presuppose a ring or associativity.")),
                    Paragraph(Text(
                        "Take the literal submodule quotient Q=mathcal A/N and its projection "
                        + "pi(x)=[x]. Postcompose m with N.mkQ and apply LinearMap.liftQ₂ to "
                        + "the two copies of N. Its kernel obligations are exactly the two "
                        + "stability statements. The resulting real bilinear M satisfies "
                        + "M(pi(x),pi(y))=pi(m(x,y)). The canonical quotient norm equals p(x) "
                        + "on pi(x): its upper bound is Submodule.Quotient.norm_mk_le; for "
                        + "the reverse bound, norm_mk_lt supplies an arbitrarily close "
                        + "representative, whose p value agrees with p(x). Thus every pair "
                        + "u,v in Q satisfies norm(M(u,v))=norm(u)norm(v), including zeros.")),
                    Paragraph(Text(
                        "A readable unit e means that p(m(e,x)-x)+p(m(x,e)-x)=0 for every "
                        + "original x. Each summand is nonnegative, so each difference belongs "
                        + "to N, and pi(e) is an exact left and right unit of M. If some p(x)>0, "
                        + "then pi(x) is nonzero; multiplying its norm by the unit shows "
                        + "norm(pi(e))=1. This norm-one conclusion requires the nonzero "
                        + "readout assumption. If p is identically zero, Q is the zero space; "
                        + "the quotient and extension constructions still apply, without "
                        + "a norm-one unit conclusion.")),
                    Paragraph(Text(
                        "More generally, let E be any real normed vector space, possibly zero "
                        + "or incomplete, with any norm-multiplicative real bilinear m. Set "
                        + "B=UniformSpace.Completion E and let i=Completion.toComplₗᵢ be the "
                        + "canonical real linear isometry. LinearMap.mkContinuous₂ with bound "
                        + "one and ContinuousLinearMap.continuous₂ make m jointly continuous. "
                        + "Compose it with i and regard it as "
                        + "a double additive homomorphism into B. IsDenseInducing.extend_Z_bilin "
                        + "along the two actual completion inclusions gives a jointly "
                        + "continuous extension f, and extend_eq gives f(i(x),i(y))=i(m(x,y)). "
                        + "Completion.induction_on₃ transports both addition laws on their "
                        + "closed equality sets; induction_on₂ transports each real scalar "
                        + "law. LinearMap.mk₂ therefore packages f as a real bilinear map. "
                        + "The same two-variable closed-set argument transports exact norm "
                        + "multiplicativity and proves uniqueness among jointly continuous "
                        + "real bilinear extensions agreeing with m.")),
                    Paragraph(Text(
                        "The closed equality f(i(e),z)=z transports an original left unit "
                        + "using Completion.induction_on. Independently, f(z,i(e))=z transports "
                        + "an original right unit. No unit or nontriviality is needed to "
                        + "construct the extension. For the original seminorm theory take E "
                        + "to be precisely Q above, with M as its multiplication. Then "
                        + "f(i(pi(x)),i(pi(y)))=i(pi(m(x,y))) and "
                        + "norm(i(pi(x)))^2=p(x)^2=q(x) for every original x,y. The same i is "
                        + "isometric and injective, so equalities between included quotient "
                        + "vectors pull back to Q, and squared-norm identities pull back to "
                        + "the original q through i composed with pi. Under nonzero readout "
                        + "and the readable unit, this completion supplies the nonzero Banach "
                        + "space and left unit for the theorem described here. Completion "
                        + "is a mathematical proof tool; original faithfulness F is neither "
                        + "used nor extended, and no new physical states are inferred.")),
                    Paragraph(Text(
                        "A compatible real inner product on the same quotient Q is available "
                        + "from Mathlib InnerProductSpace.ofNorm only after the parallelogram "
                        + "identity has been proved for its existing norm. If that identity holds "
                        + "on the actual completion B, restriction along i gives it on Q. "
                        + "Installing ofNorm on Q changes neither Q nor its norm. Its real "
                        + "polarization formula is exactly "
                        + "inner(pi(x),pi(y))=(p(x+y)^2-p(x-y)^2)/4, and "
                        + "inner(pi(x),pi(x))=p(x)^2=q(x). Thus the pulled-back form has radical "
                        + "exactly N. These are conditional consequences; invertible left "
                        + "multipliers alone are not a supplied Lean proof of the parallelogram "
                        + "premise.")),
                    Paragraph(Text(
                        "The first missing supplier in the original analytic route is Lemma 3.4: "
                        + "a complex Banach norm on B plus iB, defined by the supremum of "
                        + "norm(u cos(theta)-v sin(theta)), with complexification preserving "
                        + "every real surjective similarity factor. Lemma 3.5 then requires the "
                        + "complex operator spectrum facts. For Theorem 3.6 the same one spectral "
                        + "lambda for Lx composed with inverse Ly must work simultaneously for "
                        + "all real alpha,beta, including combinations equal to zero; y=0 is a "
                        + "separate case. That complexification supplier and the exact original "
                        + "spectral-pencil application remain unproved here. An external "
                        + "complexification implementation is not an imported or compiled "
                        + "project dependency. No unconditional real inner product, "
                        + "parallelogram identity or original Corollary 3.8 is claimed.")),
                    Paragraph(Text(
                        "Beyond that analytic gap, the original quaternion route still needs "
                        + "Theorem 4.3 on the same quotient: the same noncommuting pair must "
                        + "produce a four-dimensional quaternion subalgebra H and its orthogonal "
                        + "projection P with T=2 Lk P and kernel T equal to the orthogonal "
                        + "complement of H. Original faithfulness concerns this quotient only; "
                        + "it can force P=I through that kernel identity. The resulting isometric "
                        + "quaternion classification and global associativity in 4.5 remain "
                        + "unproved. The source equality T/(2 sqrt(q(k)))=Le, complex dimension "
                        + "two, completeness of the original quotient, and the Hopf realization "
                        + "each remain separate obligations. The full original 7.3 tensor, "
                        + "Fubini-Study normalization, quarter-area factor, connection and global "
                        + "holonomy are not conclusions of this theorem. The auxiliary complex "
                        + "space is not the original physical J.")),
                    Paragraph(Text(
                        "The mathematical source attributes the absolute-valued algebra "
                        + "background to Rodriguez Palacios, One-sided division absolute valued "
                        + "algebras, Publicacions Matematiques 36(2B), 925-954. The result is "
                        + "a source formalization; no literature originality is claimed."))),
                DescribeRole.Theorem))));
}
