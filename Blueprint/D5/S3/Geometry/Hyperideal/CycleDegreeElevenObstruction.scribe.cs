using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class CycleDegreeElevenObstructionDocument : IScribeDocumentDefinition
{
    private const string ComponentDeclaration =
        "D5/S3/Geometry/Hyperideal/CycleDegreeElevenObstruction.component_shape_and_div44";
    private const string InventoryDeclaration =
        "D5/S3/Geometry/Hyperideal/CycleDegreeElevenObstruction.inventory_tetrahedra_div88";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An 88-divisibility obstruction for pure three-cycle (8,11) packets.",
        H("An 88-divisibility obstruction for pure three-cycle (8,11) packets"),
        Blocks(
            Paragraph(Text(
                "Specialize the role-homogeneous pure three-cycle incidence theorem "
                    + "to low degree eight and high degree eleven. A center-link "
                    + "component has 2E=3N, 11V=3N and V-E+N=2-2g; globally "
                    + "the degree-eight low-edge count gives 8L=3N_total.")),
            Describe.Lean(
                DescribeId.Create("cycle-degree-eleven-component-div44"),
                DeclarationHandle.Create(ComponentDeclaration),
                H("Center-link shape and factor 44"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The center-link equations force 5N=44(g-1), hence every "
                            + "component count is divisible by 44."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cycle-degree-eleven-inventory-div88"),
                DeclarationHandle.Create(InventoryDeclaration),
                H("Global factor 88"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Summing the finite center components gives 44 dividing the "
                            + "global tetrahedron count. Combining this with the "
                            + "degree-eight low-edge factor 8 yields 88 dividing the "
                            + "global count.")),
                    Paragraph(Text(
                        "The result is a necessary topological and arithmetic "
                            + "obstruction for a role-homogeneous degree-(8,11) "
                            + "packet; it does not assert a face pairing or geometric "
                            + "realization."))),
                DescribeRole.Theorem))));
}
