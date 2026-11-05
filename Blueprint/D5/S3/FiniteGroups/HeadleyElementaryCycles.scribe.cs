using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class HeadleyElementaryCyclesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Field orbits and the small two-primary leaves", H("Field orbits and the small two-primary leaves"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("headley-elementarycycles-elementarycycle"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/HeadleyElementaryCycles.elementaryCycle"),
                H("Every elementary rank at least two"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A primitive unit in the field of cardinality two to the rank acts transitively on its nonzero additive elements. Multiplication by the primitive unit minus one permutes their directed differences, including the closing edge. A basis transports this cycle to the elementary coordinate group; rank three is included."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("headley-elementarycycles-e4rstar"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/HeadleyElementaryCycles.e4RStar"),
                H("The E4 quotient triple"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The successor traverses (1,0), (1,1), (0,1). Its differences permute the same three nonzero elements, and the first plus the third is the second."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("headley-elementarycycles-c2c4cycle"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/HeadleyElementaryCycles.c2c4Cycle"),
                H("The R-only seven-vertex leaf"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The word is (0,2), (1,3), (0,3), (1,1), (1,0), (1,2), (0,1). Its directed differences are (1,1), (1,0), (1,2), (0,3), (0,2), (1,3), (0,1), including closure. This leaf supplies an R-cycle, with no R-star assertion. These constructions belong to the Headley R-sequenceability induction; no originality claim is made."))), DescribeRole.Definition))));
}
