using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.Crossing;

internal sealed class CrossingNormalFormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The crossing discriminant is a square normal form with a unique fixed-base minimum.",
        H("Crossing Discriminant Normal Form"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("crossing-normal-form-unique-minimum"),
                DeclarationHandle.Create(
                    "D5/S3/PrimeForms/Crossing/CrossingNormalForm."
                        + "crossing_normal_form_unique_minimum"),
                H("The square term determines the unique minimum"),
                StatementSource.FromAuthor(NormalFormFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For real A and B, the crossing discriminant with offset A+B is "
                            + "3A^2+(A+B)^2. Expanding the square gives "
                            + "4A^2+2AB+B^2.")),
                    Paragraph(Text(
                        "The remaining square is nonnegative, so the discriminant is at least "
                            + "3A^2. Equality holds exactly when A+B=0, equivalently B=-A; "
                            + "therefore B=-A is the unique minimizer for each fixed A.")),
                    Paragraph(Text(
                        "This closes only the normal-form clause of pzg-v170 remark/27.393. It "
                            + "does not assert the atom's integer-surface classification, its "
                            + "polynomial-line description, or the five-class computational check.")),
                    Paragraph(Text(
                        "Repository search found and reused PrimeForms.PropagationLegs."
                            + "slotDiscriminant. Pinned-Mathlib searches found no exact theorem "
                            + "for the complete normal form or its unique minimum; the proof "
                            + "reuses add_sq, sq_nonneg, and sq_eq_zero_iff."))),
                DescribeRole.Theorem))));

    private static Formula NormalFormFormula()
    {
        Formula normal = Seq(
            D(3), F.Id("A"), Caret, D(2), Plus,
            Open, F.Id("A"), Plus, F.Id("B"), Close, Caret, D(2));

        return Disp(Seq(
            Forall, Sp, F.Id("A"), Comma, F.Id("B"), InMacro,
            Mathbb, Grp(F.Id("R")), Comma, Esc,
            normal, Eq,
            D(4), F.Id("A"), Caret, D(2), Plus,
            D(2), F.Id("A"), F.Id("B"), Plus, F.Id("B"), Caret, D(2), Sp,
            Land, Sp,
            D(3), F.Id("A"), Caret, D(2), Leq, normal, Sp,
            Land, Sp,
            Open, normal, Eq, D(3), F.Id("A"), Caret, D(2), Sp,
            Leftrightarrow, Sp, F.Id("B"), Eq, Minus, F.Id("A"), Close, Dot));
    }
}
