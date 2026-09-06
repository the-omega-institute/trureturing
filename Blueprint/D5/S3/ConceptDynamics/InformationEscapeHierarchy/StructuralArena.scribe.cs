using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscapeHierarchy;

internal sealed class StructuralArenaDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscapeHierarchy/StructuralArena.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Arbitrary state carriers support structural theorem catalogs, with finite catalogs embedded canonically.",
        H("Structural Arenas"),
        Blocks(
            DefinitionNode("structural-arena", "StructuralArena", "Structural arena",
                "A structural arena carries an arbitrary state type and imposes no finiteness or decidable-equality requirement."),
            DefinitionNode("structural-kernel", "StructuralKernel", "Structural kernel",
                "A structural kernel packages a binary relation together with its equivalence proof."),
            DefinitionNode("decidable-to-structural-kernel", "ofDecidableKernel",
                "Forget kernel decidability",
                "The finite kernel relation and equivalence proof are retained definitionally while its decision procedure is forgotten."),
            DefinitionNode("structural-theorem-unit", "StructuralTheoremUnit",
                "Structural theorem unit",
                "A proved statement carries a finite family of primitive structural kernels on the arena state type."),
            DefinitionNode("structural-catalog", "StructuralCatalog", "Structural catalog",
                "A structural catalog is a finite decidable family of structural theorem units."),
            DefinitionNode("arena-structural-embedding", "toStructuralArena",
                "Finite arena embedding",
                "The embedding forgets finite enumeration and decidable equality while preserving the state carrier."),
            DefinitionNode("theorem-unit-structural-embedding",
                "toStructuralTheoremUnit", "Finite theorem-unit embedding",
                "Every primitive kernel is embedded by forgetting only its decision procedure, and the statement proof is retained."),
            DefinitionNode("catalog-structural-embedding", "toStructuralCatalog",
                "Finite catalog embedding",
                "The finite catalog index and theorem lookup are retained while each theorem unit is structurally embedded."))));

    private static DocumentBlock.Describe DefinitionNode(
        string id, string declaration, string title, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            DescribeRole.Definition);
}
