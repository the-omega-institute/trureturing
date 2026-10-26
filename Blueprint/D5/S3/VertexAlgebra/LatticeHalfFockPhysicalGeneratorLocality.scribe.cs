using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockPhysicalGeneratorLocalityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeHalfFockPhysicalGeneratorLocality.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual tensor currents, charged slices and same-mode jets satisfy uniform finite-difference locality bounds.",
        H("Physical Generator Locality"),
        Blocks(
            Describe.Lean(DescribeId.Create("physical-generator-current-current"), DeclarationHandle.Create(Prefix + "physicalCurrent_current_locality"), H("Current-current locality"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The actual current commutator is killed by the second finite difference."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("physical-generator-current-charge"), DeclarationHandle.Create(Prefix + "physicalCurrent_charge_locality"), H("Current-charge locality"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The Ward commutator is killed by one finite difference."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("physical-generator-jet-charge"), DeclarationHandle.Create(Prefix + "physicalJet_charge_locality"), H("Jet-charge locality"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A jet of order d has a uniform order d+1 bound against every charged slice."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("physical-generator-jet-pair"), DeclarationHandle.Create(Prefix + "physicalJet_pair_locality"), H("Jet-pair locality"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Two jets have the uniform order d_i+d_j+2 bound."))), DescribeRole.Theorem),
            Paragraph(Text("The Ward identity and affine-weight finite-difference recurrence use the canonical same-mode jet formulas and make no positivity or state restriction.")))));
}
