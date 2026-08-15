using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Scale.Descent;

internal sealed class DescentWindowDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two Pell-type square bounds force a strict descent window.",
        H("Pell-Type Descent Window"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pell-type-square-bounds-force-the-descent-window"),
                DeclarationHandle.Create("D5/S1/Scale/Descent/DescentWindow.descent_window"),
                H("Square bounds force the descent window"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("c"), Comma, Sp, F.Id("T"), InMacro,
                    Mathbb, Grp(F.Id("Z")), Comma, Esc,
                    D(3), Sp, Leq, Sp, F.Id("T"), Sp, Land, Sp,
                    D(0), Sp, Leq, Sp, F.Id("c"), Sp, Land, Sp,
                    F.Id("T"), Caret, D(2), Minus, D(1), Sp, Leq, Sp,
                    F.Id("c"), Caret, D(2), Sp, Land, Sp,
                    D(3), Cdot, Sp, F.Id("c"), Caret, D(2), Sp, Leq, Sp,
                    D(4), Cdot, Sp, Grp(F.Id("T"), Caret, D(2), Minus, D(1)),
                    Sp, Rightarrow, Sp,
                    F.Id("T"), Sp, Leq, Sp, F.Id("c"), Sp, Land, Sp,
                    D(3), Cdot, Sp, F.Id("c"), Sp, Lt, Sp,
                    D(4), Cdot, Sp, F.Id("T")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let c and T be integers with T at least three and c nonnegative. If "
                        + "T squared minus one is at most c squared, while three times c squared "
                        + "is at most four times T squared minus one, then T is at most c and "
                        + "three times c is strictly less than four times T. The latter is the "
                        + "division-free form of the source window c < 4T/3.")),
                    Paragraph(Text(
                        "This is the descent-window inequality selected from the source atom. "
                        + "It does not assert the atom's separate orbit-uniqueness or finite-base "
                        + "connectivity claims. The repository and pinned Mathlib were searched "
                        + "for the full implication without an exact hit. A LeanSearch POST query "
                        + "also returned only general square and division inequalities, not this "
                        + "combined theorem. The proof therefore uses integer discreteness, "
                        + "multiplication monotonicity, ring normalization, and Presburger "
                        + "arithmetic locally."))),
                DescribeRole.Theorem))));
}
