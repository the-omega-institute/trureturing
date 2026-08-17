using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Witt;

internal sealed class WittRowLawsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first two closed Witt rows terminate or alternate with coefficients known in every degree.",
        H("Closed Laws for the First Witt Rows"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("closed-laws-for-the-first-witt-rows"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/Witt/WittRowLaws.witt_row_closed_laws"),
                H("The pure factor and both coefficient rows are explicit"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open, D(1), Plus, F.Id("X"), Close, Cdot,
                    Open, D(1), Minus, F.Id("X"), Close,
                    Eq, D(1), Minus, F.Id("X"), Caret, Grp(D(2)), Comma, RowBreak,
                    Forall, Sp, F.Id("k"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    Operatorname, Grp(F.Id("coeff")), Open, F.Id("k"), Comma, Sp,
                    Operatorname, Grp(F.Id("firstWittRow")), Close,
                    Eq, Operatorname, Grp(F.Id("if")), Open,
                    F.Id("k"), Eq, D(0), Sp, Lor, Sp, F.Id("k"), Eq, D(2), Comma,
                    Sp, D(1), Comma, Sp, D(0), Close, Comma, RowBreak,
                    Forall, Sp, F.Id("k"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    Operatorname, Grp(F.Id("coeff")), Open, F.Id("k"), Comma, Sp,
                    Operatorname, Grp(F.Id("secondWittRow")), Close,
                    Eq, Operatorname, Grp(F.Id("if")), Open,
                    F.Id("k"), Eq, D(1), Comma, Sp, D(0), Comma, Sp,
                    Open, Minus, D(1), Close, Caret, Grp(F.Id("k")), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The pure-direction factorization cancels every odd contribution. "
                            + "For the a = 1 logarithmic row, only degrees zero and two have "
                            + "coefficient one. For the b = 1 row, the linear coefficient is "
                            + "zero and every other coefficient follows the alternating sign "
                            + "pattern in all degrees.")),
                    Paragraph(Text(
                        "The proof reuses Mathlib's exact coefficient theorem for invOneSubPow "
                            + "and transports it through rescale at minus one. Formal power-series "
                            + "coefficient lemmas then identify the two closed rows; no second "
                            + "implementation of the geometric-series inverse is introduced."))),
                DescribeRole.Theorem))));
}
