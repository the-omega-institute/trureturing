using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KarpZhangGamma;

internal sealed class WeightingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite one-sign-change weighting for the gamma-series transformation.",
        H("Increasing weights"), Blocks(
            Entry("karp-zhang-gamma-weighted-sum", "weighted_sum_nonneg", "Finite weighting principle",
                "Let A and W be real sequences and h a natural number. Assume that for all i,j <= h with i < j, A(i) > 0 implies A(j) >= 0; that the sum of A(i) for 0 <= i <= h is nonnegative; that W(i) >= 0 for i <= h; and that W(i) <= W(j) for i <= j <= h. Then the sum of A(i)W(i) for 0 <= i <= h is nonnegative. Zero entries and either empty sign group are allowed."),
            Entry("karp-zhang-gamma-coefficientwise-weighting", "coefficientwise_weighting", "Coefficientwise weighting principle",
                "Let A be a real sequence, W a function from two natural indices to the reals, and h a natural number. Assume the same scalar sign condition and total-sum condition as in weighted_sum_nonneg. Assume for every natural degree N that W(i,N) is nonnegative for i <= h and W(i,N) <= W(j,N) for i <= j <= h. For every natural N the sum of A(i)W(i,N) over i=0,...,h is nonnegative."),
            Paragraph(Text("Choose the least positive term of A. Every earlier term is nonpositive and every later term is nonnegative. Subtracting the weight at that index makes each product nonnegative, while the residual constant weight multiplies the nonnegative total sum. If no positive term exists, the total-sum condition forces all terms to vanish. Applying this argument independently in each degree proves the coefficientwise statement without convergence or division of formal series.")))));

    private static DocumentBlock Entry(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/KarpZhangGamma/Weighting." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
