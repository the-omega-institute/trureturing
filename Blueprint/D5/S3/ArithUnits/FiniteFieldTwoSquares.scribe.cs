using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithUnits;

internal sealed class FiniteFieldTwoSquaresDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every residue modulo a prime is the sum of two residue squares.",
        H("Two Squares Cover Every Prime Residue Field"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("every-prime-field-element-is-a-sum-of-two-squares"),
                DeclarationHandle.Create(
                    "D5/S3/ArithUnits/FiniteFieldTwoSquares.every_element_eq_sq_add_sq"),
                H("Every prime residue is a sum of two squares"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("p"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    F.Id("p"), Esc, F.Text, Grp(F.Id("prime")), Comma, Sp,
                    Forall, Sp, F.Id("x"), InMacro, Mathbb, Grp(F.Id("Z")), Slash,
                    F.Id("p"), Mathbb, Grp(F.Id("Z")), Comma, Sp,
                    Exists, Sp, F.Id("a"), Comma, F.Id("b"), InMacro,
                    Mathbb, Grp(F.Id("Z")), Slash, F.Id("p"), Mathbb, Grp(F.Id("Z")),
                    Comma, Sp, F.Id("a"), Caret, Grp(D(2)), Plus,
                    F.Id("b"), Caret, Grp(D(2)), Eq, F.Id("x")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural prime p and every residue x modulo p, there are "
                        + "residues a and b whose squared sum is x. This includes p = 2 and "
                        + "adds no uniqueness or canonical-choice claim for the witnesses.")),
                    Paragraph(Text(
                        "Pinned Mathlib already contains the exact theorem as ZMod.sq_add_sq "
                        + "in Mathlib.FieldTheory.Finite.Basic. The Lean declaration directly "
                        + "applies that result and does not reproduce its finite-field proof."))),
                DescribeRole.Theorem))));
}
