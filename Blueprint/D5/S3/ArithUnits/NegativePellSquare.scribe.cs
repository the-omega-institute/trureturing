using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithUnits;

internal sealed class NegativePellSquareDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A norm-minus-one quadratic integer squares to an explicit norm-one Pell unit.",
        H("Squaring the Negative-Pell Unit"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("negative-pell-element-squares-to-a-pell-unit"),
                DeclarationHandle.Create(
                    "D5/S3/ArithUnits/NegativePellSquare.negative_pell_square_unit"),
                H("The negative-Pell element has an explicit norm-one square"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("j"), InMacro, Mathbb, Grp(F.Id("Z")), Comma, Quad, Sp,
                    F.Id("d"), Eq, D(3, 6), F.Id("j"), Caret, Grp(D(2)), Plus, D(1), Comma,
                    Quad, Sp, F.Id("u"), Eq, Open, D(6), F.Id("j"), Comma, Sp, D(1), Close,
                    InMacro, Operatorname, Grp(F.Id("Zsqrtd")), Open, F.Id("d"), Close, Comma,
                    Quad, Sp, Operatorname, Grp(F.Id("norm")), Open, F.Id("u"), Close, Eq,
                    Minus, D(1), Sp, Land, Sp, F.Id("u"), Caret, Grp(D(2)), Eq, Open,
                    D(7, 2), F.Id("j"), Caret, Grp(D(2)), Plus, D(1), Comma, Sp, D(1, 2),
                    F.Id("j"), Close, Sp, Land, Sp, Operatorname, Grp(F.Id("norm")), Open,
                    F.Id("u"), Caret, Grp(D(2)), Close, Eq, D(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For any integer j, put d = 36 j^2 + 1 and take the quadratic integer "
                        + "u with coordinates (6j, 1) in Zsqrtd d. Its norm is -1. Squaring u "
                        + "gives coordinates (72 j^2 + 1, 12j), and multiplicativity of the norm "
                        + "then makes this square a norm-one Pell unit.")),
                    Paragraph(Text(
                        "The formalization closes only the negative-Pell and unit-square clause of "
                        + "the source atom. It does not claim the Eisenstein-norm realization "
                        + "criterion, the finite implementation table, or the odd-core purity and "
                        + "mixed-residence conclusions from the same appendix entry.")),
                    Paragraph(Text(
                        "Repository and pinned Mathlib searches found no declaration for this "
                        + "36 j^2 + 1 parameter family. The proof reuses Mathlib revision "
                        + "fabf563a7c95a166b8d7b6efca11c8b4dc9d911f through "
                        + "Zsqrtd.normMonoidHom.map_pow for norm multiplicativity; only the explicit "
                        + "coordinate and norm computations are discharged locally. Loogle returned "
                        + "zero exact matches, and GitHub code search returned no result for the "
                        + "parameter formula."))),
                DescribeRole.Theorem
            ))));
}
