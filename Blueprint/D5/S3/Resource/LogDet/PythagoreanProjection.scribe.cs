using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Resource.LogDet;

internal sealed class PythagoreanProjectionDocument : IScribeDocumentDefinition
{
    private const string LeanPrefix = "D5/S3/Resource/LogDet/PythagoreanProjection.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A first-order certificate yields the log-determinant Pythagorean inequality, characterizes equality, and is invariant under invertible congruence.",
        H("Pythagorean Projection Certificates for Log-Det Divergence"),
        Blocks(
            Paragraph(Text(
                "The certificate is shaped like a first-order optimality condition. It records "
                + "that sigma is a positive-definite member of the feasible set and that its "
                + "inverse-difference pairing with every positive-definite feasible tau is "
                + "nonpositive. This module uses that algebraic condition directly; it does not "
                + "claim that an optimizer exists or is unique.")),
            Describe.Lean(
                DescribeId.Create("a-log-det-projection-certificate-is-a-feasible-first-order-certificate"),
                DeclarationHandle.Create(LeanPrefix + "IsLogDetProjectionCertificate"),
                H("A log-det projection certificate is a feasible first-order certificate"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Begin, F.Grp(F.Id("gathered")),
                    Certificate(F.Id("C"), F.Rho, F.SigmaLower), F.Sp,
                    F.Leftrightarrow, F.Sp, F.RowBreak, F.Sp,
                    F.SigmaLower, F.Sp, F.InMacro, F.Sp, F.Id("C"),
                    F.Sp, F.Land, F.Sp, PosDef(F.SigmaLower), F.Sp, F.Land, F.Sp,
                    F.RowBreak, F.Sp,
                    F.Forall, F.Sp, F.Tau, F.Sp, F.InMacro, F.Sp, F.Id("C"), F.Comma, F.Sp,
                    PosDef(F.Tau), F.Sp, F.Rightarrow, F.Sp,
                    Pairing(F.Rho, F.SigmaLower, F.Tau), F.Sp, F.Le, F.Sp, F.D(0),
                    F.Dot, F.End, F.Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The universal inequality is exactly the remainder in the frozen three-point "
                    + "identity. Positive definiteness is required only for feasible comparison "
                    + "points used by the certificate."))),
                DescribeRole.Definition
            ),
            Describe.Lean(
                DescribeId.Create("congruence-image-transforms-every-feasible-matrix"),
                DeclarationHandle.Create(LeanPrefix + "congruenceImage"),
                H("The congruence image transforms every feasible matrix"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    CongruenceImage(F.Id("T"), F.Id("C")), F.Sp, F.Eq, F.Sp,
                    F.OpenBrace, Congruence(F.Id("T"), F.Id("A")), F.Sp,
                    F.Mid, F.Sp, F.Id("A"), F.Sp, F.InMacro, F.Sp, F.Id("C"),
                    F.CloseBrace))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The image set consists precisely of matrices T A T "
                    + "conjugate-transpose with A in the original feasible set."))),
                DescribeRole.Definition
            ),
            Describe.Lean(
                DescribeId.Create("a-log-det-projection-certificate-implies-the-pythagorean-inequality"),
                DeclarationHandle.Create(LeanPrefix + "pythagorean"),
                H("A log-det projection certificate implies the Pythagorean inequality"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Begin, F.Grp(F.Id("gathered")),
                    Certificate(F.Id("C"), F.Rho, F.SigmaLower), F.Sp,
                    F.Land, F.Sp, PosDef(F.Rho), F.Sp, F.Rightarrow, F.Sp,
                    F.RowBreak, F.Sp,
                    F.Forall, F.Sp, F.Tau, F.Sp, F.InMacro, F.Sp, F.Id("C"), F.Comma, F.Sp,
                    PosDef(F.Tau), F.Sp, F.Rightarrow, F.Sp, F.RowBreak, F.Sp,
                    LogDet(F.Rho, F.SigmaLower), F.Sp, F.Plus, F.Sp,
                    LogDet(F.SigmaLower, F.Tau), F.Sp, F.Le, F.Sp,
                    LogDet(F.Rho, F.Tau), F.Dot,
                    F.End, F.Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The frozen three-point identity rewrites the difference between the two "
                    + "sides as the certificate pairing. Its nonpositivity is exactly the stated "
                    + "Pythagorean inequality."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("equality-in-the-log-det-pythagorean-law-is-orthogonality"),
                DeclarationHandle.Create(LeanPrefix + "logDetDivergence_pythagorean_eq_iff"),
                H("Equality in the log-det Pythagorean law is orthogonality"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Begin, F.Grp(F.Id("gathered")),
                    PosDef(F.Rho), F.Sp, F.Land, F.Sp, PosDef(F.SigmaLower),
                    F.Sp, F.Land, F.Sp, PosDef(F.Tau), F.Sp, F.Rightarrow, F.Sp,
                    F.RowBreak, F.Sp,
                    F.Open, LogDet(F.Rho, F.SigmaLower), F.Sp, F.Plus, F.Sp,
                    LogDet(F.SigmaLower, F.Tau), F.Sp, F.Eq, F.Sp,
                    LogDet(F.Rho, F.Tau), F.Close, F.Sp, F.Leftrightarrow, F.Sp,
                    F.RowBreak, F.Sp,
                    Pairing(F.Rho, F.SigmaLower, F.Tau), F.Sp, F.Eq, F.Sp, F.D(0),
                    F.Dot, F.End, F.Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Rearranging the same three-point identity shows that equality holds exactly "
                    + "when the inverse-difference pairing vanishes. No optimizer interpretation "
                    + "is needed for this equivalence."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("log-det-projection-certificates-are-invariant-under-invertible-congruence"),
                DeclarationHandle.Create(LeanPrefix + "congruence"),
                H("Log-det projection certificates are invariant under invertible congruence"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Begin, F.Grp(F.Id("gathered")),
                    Certificate(F.Id("C"), F.Rho, F.SigmaLower), F.Sp,
                    F.Land, F.Sp, IsUnitDet(F.Id("T")), F.Sp, F.Rightarrow, F.Sp,
                    F.RowBreak, F.Sp,
                    Certificate(
                        CongruenceImage(F.Id("T"), F.Id("C")),
                        Congruence(F.Id("T"), F.Rho),
                        Congruence(F.Id("T"), F.SigmaLower)), F.Dot,
                    F.End, F.Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Invertible congruence preserves positive definiteness and feasible-set "
                    + "membership. Reversing the congruence products under inversion, cancelling "
                    + "T inverse times T, and cycling the trace show that the transformed pairing "
                    + "equals the original pairing, so the certificate inequality transports."))),
                DescribeRole.Theorem))));

    private static Formula Certificate(Formula set, Formula rho, Formula sigma) => F.Seq(
        F.Operatorname, F.Grp(F.Id("IsLogDetProjectionCertificate")), F.Open,
        set, F.Comma, F.Sp, rho, F.Comma, F.Sp, sigma, F.Close);

    private static Formula CongruenceImage(Formula transform, Formula set) => F.Seq(
        F.Operatorname, F.Grp(F.Id("congruenceImage")), F.Open,
        transform, F.Comma, F.Sp, set, F.Close);

    private static Formula Congruence(Formula transform, Formula matrix) => F.Seq(
        transform, F.Sp, matrix, F.Sp,
        transform, F.Caret, F.Grp(F.Id("H")));

    private static Formula LogDet(Formula left, Formula right) => F.Seq(
        F.Operatorname, F.Grp(F.Id("logDetDivergence")), F.Open,
        left, F.Comma, F.Sp, right, F.Close);

    private static Formula PosDef(Formula matrix) => F.Seq(
        F.Operatorname, F.Grp(F.Id("PosDef")), F.Open, matrix, F.Close);

    private static Formula IsUnitDet(Formula matrix) => F.Seq(
        F.Operatorname, F.Grp(F.Id("IsUnit")), F.Open,
        F.Operatorname, F.Grp(F.Id("det")), F.Open, matrix, F.Close, F.Close);

    private static Formula Pairing(Formula rho, Formula sigma, Formula tau) => F.Seq(
        F.Re, F.Grp(
            F.Operatorname, F.Grp(F.Id("tr")), F.Open,
            F.Open, Inverse(sigma), F.Sp, F.Minus, F.Sp, Inverse(tau), F.Close, F.Sp,
            F.Open, rho, F.Sp, F.Minus, F.Sp, sigma, F.Close,
            F.Close));

    private static Formula Inverse(Formula matrix) => F.Seq(
        matrix, F.Caret, F.Grp(F.Minus, F.D(1)));
}
