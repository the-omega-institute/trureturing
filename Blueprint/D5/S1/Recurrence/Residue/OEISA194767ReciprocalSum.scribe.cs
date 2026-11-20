using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class OEISA194767ReciprocalSumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Residue/OEISA194767ReciprocalSum.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/mazhang2026a189733siblings");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The reciprocals of the fourth-diagonal denominators of the A194767 second-kind array "
            + "sum to 1 + log 3 − π/(3√3).",
        H("Reciprocal sum of the A194767 fourth-diagonal denominators"),
        Blocks(
            Describe.Lean(DescribeId.Create("a194767-reciprocal-sum"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The reciprocal sum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Let d_m be the reduced denominator of the fourth diagonal C(m, m + 3) of "
                    + "the second-kind array. The real series ∑_{m≥0} 1/d_m has sum "
                    + "1 + log 3 − π/(3√3). The residue formulas for d_m give the partial sum "
                    + "over m < 3N as 1 − 1/(3N + 1) + 2 ∑_{k<N} (1/(3k + 2) − 1/(3k + 3)). "
                    + "The inner sum equals ∫_0^1 (x − x^{3N+1})/(1 + x + x²) dx. The tail "
                    + "integral of x^{3N+1}/(1 + x + x²) lies between 0 and 1/(3N + 2). "
                    + "The fundamental theorem of calculus with the antiderivative "
                    + "½ log(x² + x + 1) − (1/√3) arctan((2x + 1)/√3) gives "
                    + "∫_0^1 x/(1 + x + x²) dx = ½ log 3 − π/(6√3). The partial sums of nonnegative terms "
                    + "are monotone, so the subsequence limit is the sum. This is Corollary 8 "
                    + "of H. Ma and W. Zhang's note (DOI 10.5281/zenodo.23957584)."))),
                DescribeRole.Theorem))));
}
