using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Resource.LogDet;

internal sealed class CongruenceGeometryDocument : IScribeDocumentDefinition
{
    private const string LeanPrefix = "D5/S3/Resource/LogDet/CongruenceGeometry.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The log-determinant divergence is invariant under invertible congruence, satisfies a three-point identity, and is not symmetric.",
        H("Congruence Geometry of the Log-Determinant Divergence"),
        Blocks(
            Paragraph(Text(
                "The total matrix definition remains invariant when both arguments are transformed "
                + "by the same invertible congruence. No invertibility assumption on sigma is "
                + "needed: nonsingular matrix inversion reverses products unconditionally, while "
                + "the single hypothesis on T supplies exactly the cancellations used by the "
                + "resulting similarity.")),
            Describe.Lean(
                DescribeId.Create("log-det-divergence-is-invariant-under-invertible-congruence"),
                DeclarationHandle.Create(LeanPrefix + "logDetDivergence_conjugate_congr"),
                H("Log-det divergence is invariant under invertible congruence"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Operatorname, F.Grp(F.Id("IsUnit")), F.Open,
                    F.Operatorname, F.Grp(F.Id("det")), F.Open, F.Id("T"), F.Close,
                    F.Close, F.Sp, F.Rightarrow, F.Sp,
                    LogDet(
                        F.Seq(F.Id("T"), F.Sp, F.Rho, F.Sp, ConjTransposeT()),
                        F.Seq(F.Id("T"), F.Sp, F.SigmaLower, F.Sp, ConjTransposeT())),
                    F.Sp, F.Eq, F.Sp, LogDet(F.Rho, F.SigmaLower)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "After expanding the inverse of T sigma T conjugate-transpose, the quotient "
                    + "is similar to sigma inverse times rho through T conjugate-transpose. Trace "
                    + "cycling and determinant multiplicativity remove that similarity, including "
                    + "when sigma is singular under the total junk-value convention."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("log-det-divergence-satisfies-the-three-point-identity"),
                DeclarationHandle.Create(LeanPrefix + "logDetDivergence_three_point"),
                H("Log-det divergence satisfies the three-point identity"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    PosDef(F.Rho), F.Sp, F.Land, F.Sp, PosDef(F.SigmaLower),
                    F.Sp, F.Land, F.Sp, PosDef(F.Tau), F.Sp, F.Rightarrow, F.Sp,
                    LogDet(F.Rho, F.SigmaLower), F.Sp, F.Plus, F.Sp,
                    LogDet(F.SigmaLower, F.Tau), F.Sp, F.Minus, F.Sp,
                    LogDet(F.Rho, F.Tau), F.Sp, F.Eq, F.Sp,
                    F.Re, F.Grp(
                        F.Operatorname, F.Grp(F.Id("tr")), F.Open,
                        F.Open, Inverse(F.SigmaLower), F.Sp, F.Minus, F.Sp,
                        Inverse(F.Tau), F.Close, F.Sp,
                        F.Open, F.Rho, F.Sp, F.Minus, F.Sp, F.SigmaLower, F.Close,
                        F.Close)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Three applications of the barrier Bregman identity cancel every barrier "
                    + "height. Distributing the remaining matrix products and using linearity of "
                    + "the trace leaves the stated inverse-difference pairing."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("log-det-divergence-is-not-symmetric"),
                DeclarationHandle.Create(LeanPrefix + "exists_logDetDivergence_ne_swap"),
                H("Log-det divergence is not symmetric"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Exists, F.Sp, F.Rho, F.Comma, F.Sp, F.SigmaLower, F.Colon, F.Sp,
                    MatrixFinOneType(), F.Comma, F.Sp,
                    PosDef(F.Rho), F.Sp, F.Land, F.Sp, PosDef(F.SigmaLower),
                    F.Sp, F.Land, F.Sp,
                    LogDet(F.Rho, F.SigmaLower), F.Sp, F.Neq, F.Sp,
                    LogDet(F.SigmaLower, F.Rho)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In dimension one, take rho to be the diagonal matrix with entry two and "
                    + "sigma to be the identity. Both are positive definite, while equality of "
                    + "the two divergence orders would force three halves minus twice log two to "
                    + "vanish. The certified upper bound for log two makes that quantity strictly "
                    + "positive."))),
                DescribeRole.Theorem))));

    private static Formula LogDet(Formula left, Formula right) => F.Seq(
        F.Operatorname, F.Grp(F.Id("logDetDivergence")), F.Open,
        left, F.Comma, F.Sp, right, F.Close);

    private static Formula PosDef(Formula matrix) => F.Seq(
        F.Operatorname, F.Grp(F.Id("PosDef")), F.Open, matrix, F.Close);

    private static Formula Inverse(Formula matrix) => F.Seq(
        matrix, F.Caret, F.Grp(F.Minus, F.D(1)));

    private static Formula ConjTransposeT() => F.Seq(
        F.Id("T"), F.Caret, F.Grp(F.Id("H")));

    private static Formula MatrixFinOneType() => F.Seq(
        F.Operatorname, F.Grp(F.Id("Matrix")), F.Open,
        F.Operatorname, F.Grp(F.Id("Fin")), F.Open, F.D(1), F.Close,
        F.Comma, F.Sp,
        F.Operatorname, F.Grp(F.Id("Fin")), F.Open, F.D(1), F.Close,
        F.Comma, F.Sp, F.Mathbb, F.Grp(F.Id("C")), F.Close);
}
