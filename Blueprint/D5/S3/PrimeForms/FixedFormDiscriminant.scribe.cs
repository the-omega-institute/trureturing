using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms;

internal sealed class FixedFormDiscriminantDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("The fixed-point form discriminant of a 2x2 integer matrix equals tr^2 - 4 det; at determinant -1 it is tr^2 + 4.",
        H("Fixed-Form Discriminant"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("det-neg-one-fixed-form-disc"),
                DeclarationHandle.Create("D5/S3/PrimeForms/FixedFormDiscriminant.det_neg_one_fixed_form_disc"),
                H("At determinant minus one the fixed-form discriminant is trace squared plus four"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("a"), F.Id("d"), Minus, F.Id("b"), F.Id("c"), Eq, Minus, D(1),
                    Sp, Rightarrow, Sp,
                    Open, F.Id("d"), Minus, F.Id("a"), Close, Caret, Grp(D(2)), Plus,
                    D(4), F.Id("b"), F.Id("c"), Eq,
                    Open, F.Id("a"), Plus, F.Id("d"), Close, Caret, Grp(D(2)), Plus, D(4)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The fixed-point equation x = (a x + b)/(c x + d) of a 2x2 integer matrix [[a,b],[c,d]] "
                        + "gives the quadratic c x^2 + (d - a) x - b, whose discriminant is (d - a)^2 + 4 b c. "
                        + "By the ring identity this equals (a + d)^2 - 4(a d - b c) = tr^2 - 4 det. When the "
                        + "determinant a d - b c is -1, the discriminant is exactly tr^2 + 4.")),
                    Paragraph(Text(
                        "For the pinned odd core of trace 12 j (determinant -1), the discriminant specialises to "
                        + "(12 j)^2 + 4 = 4(36 j^2 + 1), exactly four times the negative-Pell discriminant "
                        + "d_j = 36 j^2 + 1. No claim is made about class-equivalence or the minimum of the core "
                        + "form beyond this discriminant identity."))),
                DescribeRole.Theorem))));
}
