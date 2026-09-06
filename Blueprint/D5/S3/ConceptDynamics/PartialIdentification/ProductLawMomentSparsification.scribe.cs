using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.PartialIdentification;

internal sealed class ProductLawMomentSparsificationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/PartialIdentification/ProductLawMomentSparsification.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A first compression preserves all joint moments with the right law fixed. A second compression uses the new left law and preserves the same moment vector. Both endpoints remain products of normalized rational component laws.",
        H("Sequential sparsification inside a product family"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("left-slice"),
                DeclarationHandle.Create(Prefix + "product_linearObjective_eq_left"),
                H("Exact fixed-right linear slice"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Finite sum expansion treats any rational joint coefficient, including signed moments, as a linear objective in the left law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("right-slice"),
                DeclarationHandle.Create(Prefix + "product_linearObjective_eq_right"),
                H("Exact fixed-left linear slice"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The symmetric sum identity supplies the second compression after the first component has been replaced."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("product-moment-sparse-replacements"),
                DeclarationHandle.Create(Prefix + "productLaw_moment_sparse_replacements"),
                H("Preserve joint moments with sparse independent factors"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For d nominated joint moments, each factor can be replaced by a law with at most d+1 nonzero masses. The second feature map is recomputed using the compressed first law. Global convexity is unnecessary."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("product-linear-problem-sparse-witness"),
                DeclarationHandle.Create(Prefix + "product_linear_problem_sparse_witness"),
                H("Preserve all data rows and the target in the product family"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Keeping m rational constraint values and one objective value gives at most m+2 support points per factor. The original linear feasibility predicate and objective remain unchanged, while the product restriction is retained explicitly."))),
                DescribeRole.Theorem))));
}
