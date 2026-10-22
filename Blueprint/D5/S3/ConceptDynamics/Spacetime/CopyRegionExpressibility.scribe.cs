using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Spacetime;

internal sealed class CopyRegionExpressibilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Spacetime/CopyRegionExpressibility.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The copy version of Proposition 64 is conditional on the explicit profile and saturation laws.",
        H("Copy Region Expressibility"),
        Blocks(
            Describe.Lean(DescribeId.Create("proposition-64"), DeclarationHandle.Create(Prefix + "Proposition64"),
                H("Copy expressibility exactly characterizes Tail"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Proposition64 states the source quantifiers: a positive finite total diagonal copy expression exists exactly when the region has a uniform past tail."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("three-way"), DeclarationHandle.Create(Prefix + "Proposition64ThreeWay"),
                H("Copy, one-hole and tail forms"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The three-way predicate records agreement of copy expressibility with the existing one-hole QExpressible criterion and Tail."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("conditional-two-way"), DeclarationHandle.Create(Prefix + "proposition64_of_profile_and_saturation"),
                H("Conditional Proposition 64"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact two-way proposition is proved from the named finite slice-readout and joint-saturation premises."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("conditional-three-way"), DeclarationHandle.Create(Prefix + "proposition64_three_way_of_profile_and_saturation"),
                H("Conditional three-way equivalence"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact three-way equivalence follows from the same premises and the frozen one-hole criterion."))), DescribeRole.Theorem)
        ),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ConceptDynamics/Spacetime/RegionFilterQExpressibility"))
        ]));
}
