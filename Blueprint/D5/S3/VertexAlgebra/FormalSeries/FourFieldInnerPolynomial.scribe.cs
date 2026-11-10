using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.FormalSeries;

internal sealed class FourFieldInnerPolynomialDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/FormalSeries/FourFieldInnerPolynomial.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal four-field clearing", H("Literal four-field clearing"), Blocks(
            Describe.Lean(DescribeId.Create("fourfieldinnerpolynomial-inner-action-expansion"),
                DeclarationHandle.Create(Prefix + "inner_action_expansion"),
                H("Literal four-field clearing"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any complex module and arbitrary signed four-variable coefficient distribution F, finite Laurent convolution by the full polynomial R equals the five-index finite clearing expression. The polynomial contains the four original monomial factors, the untouched spectator pair, all four spectator-to-inner cross factors and b to the locality order. The five binomial indices expand only finite polynomial factors. The resulting shifts are x-a0-3k+h+p0+q0 and y-a1-2k-h+p1+q1, with inner exponents a2+p0+p1 and a3+q0+q1. This statement neither substitutes a raw distribution nor assumes an iterate identity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fourfieldinnerpolynomial-clearing-four"),
                DeclarationHandle.Create(Prefix + "clearing_four"),
                H("All six pair factors"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The product over all six labelled pairs factors into the inner t-position minus q-position factor and the five remaining cross factors. On arbitrary signed distributions its finite polynomial action is the bivariate inner clearing of the five-index cross convolution. The labels retain their original coordinates."))), DescribeRole.Theorem))));
}
