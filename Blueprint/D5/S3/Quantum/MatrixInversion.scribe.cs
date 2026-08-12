using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;

internal sealed class MatrixInversionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Weighted matrix inverses factor through an affine segment in noncommutative order.",
        H("Affine Matrix Inversion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("weighted-inverses-factor-through-the-affine-segment"),
                DeclarationHandle.Create("D5/S3/Quantum/MatrixInversion.positive_definite_inversion_identity"),
                H("Weighted inverses factor through the affine segment"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, Rho, Comma, SigmaLower, Sp, InMacro, Sp,
                    F.Id("M"), Underscore, Grp(F.Id("n")), Open, Mathbb, Grp(F.Id("C")), Close,
                    Comma, Esc, Forall, Sp, F.Id("a"), Comma, F.Id("b"), Comma, F.Id("u"),
                    Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Esc,
                    Rho, Gt, D(0), Sp, Land, Sp, SigmaLower, Gt, D(0), Sp, Land, Sp,
                    F.Id("a"), Gt, D(0), Sp, Land, Sp, F.Id("b"), Gt, D(0), Sp, Land, Sp,
                    D(0), Leq, Sp, F.Id("u"), Leq, D(1), Sp, Rightarrow, Sp,
                    Open,
                    F.Id("a"), Cdot, Rho, Caret, Grp(Minus, D(1)), Plus,
                    F.Id("b"), Cdot, SigmaLower, Caret, Grp(Minus, D(1)), Eq,
                    Rho, Caret, Grp(Minus, D(1)), Cdot,
                    Open, F.Id("a"), Cdot, SigmaLower, Plus, F.Id("b"), Cdot, Rho, Close,
                    Cdot, SigmaLower, Caret, Grp(Minus, D(1)),
                    Close, Sp, Land, Sp,
                    Open,
                    Open, D(1), Minus, F.Id("u"), Close, Cdot,
                    Rho, Caret, Grp(Minus, D(1)), Plus,
                    F.Id("u"), Cdot, SigmaLower, Caret, Grp(Minus, D(1)),
                    Close, Caret, Grp(Minus, D(1)), Eq,
                    SigmaLower, Cdot,
                    Open,
                    Open, D(1), Minus, F.Id("u"), Close, Cdot, SigmaLower, Plus,
                    F.Id("u"), Cdot, Rho,
                    Close, Caret, Grp(Minus, D(1)), Cdot, Rho))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive-definite finite square complex matrices rho and sigma, positive real "
                    + "numbers a and b, and u in the closed unit interval, the weighted inverse sum "
                    + "factors through the affine segment. The inverse of the corresponding weighted "
                    + "sum is sigma times the inverse segment times rho, in that order. No commutativity "
                    + "of rho and sigma is assumed. The formal module also exposes the factorization "
                    + "and affine inverse identity as independent interfaces."))),
                DescribeRole.Lemma))));
}
