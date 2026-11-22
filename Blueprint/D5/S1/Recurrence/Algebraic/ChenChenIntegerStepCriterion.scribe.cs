using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class ChenChenIntegerStepCriterionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/ChenChenIntegerStepCriterion.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/mazhang2026chenchenparity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For integer m, the positive even rows of the step-m Eulerian triangle are nonnegative "
            + "exactly when m ≤ −3 or m ≥ 0, and then strictly positive.",
        H("Integer steps with nonnegative even rows"),
        Blocks(
            Describe.Lean(DescribeId.Create("chen-chen-integer-step-criterion-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The integer-step criterion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every integer m, every solution of the step-m recursion has entrywise "
                    + "nonnegative positive even rows if and only if m ≤ −3 or m ≥ 0, and for "
                    + "these m the positive even rows are strictly positive. For m ≥ 0 both "
                    + "coefficients m(n−k)+1 and m(k−1)+1 are at least one, so induction on rows "
                    + "makes every entry of every row positive. For m ≤ −3 the sign theorem "
                    + "for real r=−m ≥ 3 applies. For m=−1 and m=−2, every solution has "
                    + "T(4,2)=2m+1+2(m+1)²=2m²+6m+3=−1, and a solution exists, so the "
                    + "even row n=4 is not nonnegative. This is Corollary 3 of H. Ma and "
                    + "W. Zhang's proof of Chen and Chen's parity-positivity conjectures "
                    + "(DOI 10.5281/zenodo.23957560)."))),
                DescribeRole.Theorem))));
}
