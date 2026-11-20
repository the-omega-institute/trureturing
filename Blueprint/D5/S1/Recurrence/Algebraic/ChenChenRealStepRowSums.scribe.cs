using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class ChenChenRealStepRowSumsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/ChenChenRealStepRowSums.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/mazhang2026chenchenparity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For real m, the rows of the step-m Eulerian triangle sum to ∏(mj+2), and even rows "
            + "have vanishing alternating sum and equal parity sums.",
        H("Row sums and parity sums of the real-step Eulerian triangle"),
        Blocks(
            Describe.Lean(DescribeId.Create("chen-chen-real-step-row-sums-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Row-sum product and even-row parity sums"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Let m be real and let T satisfy T(n,1)=T(n,n)=1 for n ≥ 1 and "
                    + "T(n,k)=(m(n−k)+1)T(n−1,k−1)+(m(k−1)+1)T(n−1,k) for 1<k<n, the "
                    + "step-m Eulerian triangle of X. Chen and Y. Chen (OEIS A392664–A392666). "
                    + "Then for every n ≥ 1, ∑_{k=1}^{n} T(n,k)=∏_{j=0}^{n−2}(mj+2); and for "
                    + "every even n, ∑_{k=1}^{n} (−1)^{k−1}T(n,k)=0, so the entries at odd "
                    + "positions and the entries at even positions each sum to half the row "
                    + "sum. Pad row n−1 by zero outside 1 ≤ k ≤ n−1; the recursion then holds at "
                    + "every position of row n, including the two boundary positions. Summing "
                    + "it, the entry of row n−1 at position j receives total coefficient "
                    + "(m(n−1−j)+1)+(m(j−1)+1)=m(n−2)+2, so S(n)=(m(n−2)+2)S(n−1) and "
                    + "S(1)=1. The two recursion coefficients exchange under k ↦ n+1−k, so "
                    + "T(n,k)=T(n,n+1−k) by induction on rows. For even n this reflection pairs "
                    + "positions of opposite parity, so the alternating sum equals its own "
                    + "negative. These identities are Corollary 4 of H. Ma and W. Zhang's proof "
                    + "of Chen and Chen's parity-positivity conjectures "
                    + "(DOI 10.5281/zenodo.23957560)."))),
                DescribeRole.Theorem))));
}
