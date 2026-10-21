using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.MultipartiteCHS;

internal sealed class RecurrenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Elementary symmetric polynomials of part sizes and reciprocal coefficients.",
        H("Multipartite CHS recurrence"),
        Blocks(
            Paragraph(Text("The module proves nonnegativity of every coefficient and strict positivity of the even coefficients when there are at least two positive parts. The extremal comparison is proved in the Extremal module and transferred to CHS norms in the Result module.")),
            Describe.Lean(DescribeId.Create("multipartite-esymm-parts"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/MultipartiteCHS/Recurrence.esymmParts"),
                H("Elementary symmetric part sum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a part-size function a, esymmParts a j sums the products over all j-element subsets of the part indices."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("multipartite-reciprocal-coefficients"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/MultipartiteCHS/Recurrence.recH"),
                H("Reciprocal coefficient sequence"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("recH is defined by strong induction. Its constant coefficient is one, and each positive degree is obtained by the finite convolution with the coefficients (j minus one) times esymmParts a j."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("multipartite-recurrence-zero"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/MultipartiteCHS/Recurrence.recH_zero"),
                H("Constant coefficient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The reciprocal coefficient sequence starts at one."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("multipartite-recurrence-equation"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/MultipartiteCHS/Recurrence.recH_eq"),
                H("Coefficient recurrence"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Every positive coefficient is the sum of the lower coefficients weighted by the elementary symmetric part sums."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("multipartite-recurrence-nonnegative"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/MultipartiteCHS/Recurrence.recH_nonneg"),
                H("Nonnegative coefficients"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("All reciprocal coefficients are nonnegative over the real numbers."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("multipartite-recurrence-positive"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/MultipartiteCHS/Recurrence.recH_two_mul_pos"),
                H("Positive even coefficients"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("With at least two positive parts, every positive even coefficient is strictly positive."))), DescribeRole.Theorem))));
}
