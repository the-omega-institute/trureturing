using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Spacetime;

internal sealed class CopyRegionExpressibilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Spacetime/NativeTimeProfile.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive total native copy expressibility is equivalent to the uniform past-tail criterion.",
        H("Copy Region Expressibility"),
        Blocks(
            Describe.Lean(DescribeId.Create("two-way"), DeclarationHandle.Create(Prefix + "proposition64"),
                H("Proposition 64"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every region, the exact positive-arity all-input copy criterion is equivalent to Tail. Necessity uses the native profile polynomial, its full linear coefficient, and finite joint saturation; sufficiency reuses the frozen one-hole construction. No profile or saturation assumptions remain."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("three-way-theorem"), DeclarationHandle.Create(Prefix + "proposition64_three_way"),
                H("Three-way equivalence"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every region, copy expressibility is equivalent to the conjunction of the existing one-hole QExpressible criterion and Tail. The copy necessity retains the native polynomial proof on its live dependency path."))), DescribeRole.Theorem)
        ),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ConceptDynamics/Spacetime/RegionFilterQExpressibility"))
        ]));
}
