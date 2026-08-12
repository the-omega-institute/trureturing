using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer;

internal sealed class ConditioningCertificateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The matrix defect of finite record conditioning vanishes exactly, without a tolerance term.",
        H("Exact Conditioning Certificate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("the-conditioning-certificate-defect-vanishes-exactly"),
                DeclarationHandle.Create("D5/S3/Observer/ConditioningCertificate.certificate_identity_zero_tolerance"),
                H("The conditioning certificate defect vanishes exactly"),
                StatementSource.FromAuthor(CertificateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                                    "Let P be a finite complete family of pairwise orthogonal self-adjoint "
                                    + "projections and let rho be positive semidefinite. Define the certificate "
                                    + "defect as the unread matrix minus the record-weighted ensemble of the totalized "
                                    + "conditional branches. Zero-weight branches cause no residual because their "
                                    + "positive compressed blocks vanish. The established weighted-ensemble "
                                    + "identity therefore makes the matrix-valued defect exactly zero; no norm, "
                                    + "error bound, or approximation parameter is introduced."))),
                DescribeRole.Theorem
            ))));

    private static Formula CertificateFormula() => Disp(Seq(
        Ambient(),
        RecordPremise(), Sp, Land, Sp,
        Operatorname, Grp(F.Id("PosSemidef")), Open, Rho, Close,
        Sp, Rightarrow, RowBreak,
        Defect(), Eq, D(0),
        Comma, Quad, Sp,
        Defect(), Colon, Eq,
        Unread(), Minus,
        Sum, Underscore, Grp(F.Id("k"), InMacro, Kappa),
        Weight(), Cdot, Sp, Branch(), Dot));

    private static Formula Ambient() => Seq(
        Forall, Sp, F.Id("n"), Comma, Kappa, Esc,
        OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, F.Id("n"), Close,
        CloseBracket, Esc,
        OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, Kappa, Close,
        CloseBracket, Comma, RowBreak,
        Forall, Sp, F.Id("P"), Colon, Sp, Kappa, To, Sp, MatrixType(), Comma, Esc,
        Rho, InMacro, Sp, MatrixType(), Comma, RowBreak);

    private static Formula MatrixType() => Seq(
        F.Id("M"), Underscore, Grp(F.Id("n")),
        Open, Mathbb, Grp(F.Id("C")), Close);

    private static Formula RecordPremise() => Seq(
        Operatorname, Grp(F.Id("Record")), Open, F.Id("P"), Close);

    private static Formula Defect() => Seq(
        F.Id("d"), Underscore, Grp(F.Id("P")), Open, Rho, Close);

    private static Formula Unread() => Seq(
        F.Id("U"), Underscore, Grp(F.Id("P")), Open, Rho, Close);

    private static Formula Weight() => Seq(
        F.Id("w"), Underscore, Grp(F.Id("k")), Open, Rho, Close);

    private static Formula Branch() => Seq(
        Rho, Underscore, Grp(F.Id("k")));
}
