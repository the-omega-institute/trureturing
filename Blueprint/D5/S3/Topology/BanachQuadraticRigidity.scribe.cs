using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class BanachQuadraticRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distance conservation for the original symmetric quadratic equation in an arbitrary real Banach space.",
        H("Quadratic ODE distance conservation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("banach-quadratic-solution-distance"),
                DeclarationHandle.Create("D5/S3/Topology/BanachQuadraticRigidity.quadratic_solution_dist_eq"),
                H("Two solutions preserve distance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let E be any complete real normed vector space, including the zero space, "
                        + "and B a continuous real bilinear map from E times E to E. Suppose B is "
                        + "symmetric and, for every x in E and every real h, the exponential of "
                        + "h times the operator B(x,-) is an isometry in the given norm. On any "
                        + "open connected subset s of the real line, let x and y both solve "
                        + "z'=B(z,z) at every time in s. Then dist(x(t),y(t)) equals "
                        + "dist(x(u),y(u)) for every t,u in s. No finite dimension, inner product, "
                        + "nonzero carrier or supplied global flow is assumed.")),
                    Paragraph(Text(
                        "At a fixed time v freeze A=B(x(v)+y(v),-). Bilinearity and symmetry "
                        + "give (x-y)'(v)=A(x(v)-y(v)). The frozen orbit "
                        + "exp((w-v)A)(x(v)-y(v)) has the same value and derivative at v. "
                        + "Their difference is o(|w-v|). The reverse triangle inequality "
                        + "bounds the change of norms by this difference, while exponential "
                        + "isometry makes the orbit norm constant. Thus the norm of x-y has "
                        + "derivative zero, even when the ambient norm is not differentiable. "
                        + "The mean value theorem on the open connected time domain gives "
                        + "the asserted distance identity. The exponential derivative and "
                        + "mean value theorem are used directly from pinned Mathlib."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The intended source application is the quadratic-flow step after (2.8) in "
                + "AURIC_ARBITRARY_DIMENSIONAL_SMALL_WINDOW_UNIT_BRIDGE. It uses the same "
                + "completed space, the same original symmetric S, K=T-I, and "
                + "B(a,b)=K(S(a,b))-S(K(a),b)-S(a,K(b)). Once that B and its exponential "
                + "isometry hypotheses are supplied, the theorem applies to any two of its "
                + "actual quadratic solutions on their common open time interval. Taking "
                + "the second curve to be zero yields constant solution norm; taking two "
                + "curves with the same initial state yields uniqueness on that interval.")),
            Paragraph(Text(
                "The full arbitrary Banach-space implication from symmetry and all exponential "
                + "isometries to B=0 remains a separate obligation. This distance theorem "
                + "does not supply local existence, uniform continuation on invariant balls, "
                + "a global flow or its surjectivity. Completing those steps would allow "
                + "Mazur-Ulam, differentiation of the resulting linear flow at time zero, "
                + "and polarization to prove B=0. The source-specific same-S derivation, "
                + "the actual operators A_h, K=0, and the original unit law also remain "
                + "outside this local result. The already formalized dominated scalar "
                + "operator rigidity is not reproved here."))),
        []));
}
