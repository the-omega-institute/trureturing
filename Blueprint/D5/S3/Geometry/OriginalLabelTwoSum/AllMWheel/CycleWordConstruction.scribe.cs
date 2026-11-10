using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel;
internal sealed class CycleWordConstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        DefinitionDsl.GeneralHeader(
            "D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWordConstruction",
            "Occurrence and attachment Word constructors.",
            "original-coordinate-constructions",
            Anchor.ParseCanonical("mathlib/module/Mathlib.Order.UpperLower.CompleteLattice")),
        H("Occurrence and attachment Word constructors"),
        Blocks(
            Paragraph(Text("Occurrence splitting, paired-cone lists and attachment words retain the original finite grounds, partition, coverage and dependency order. The public constructors below are consumed by the actual cycle Word.")),
            Describe.Lean(DescribeId.Create("attachfamily"),
                DeclarationHandle.Create("D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWordConstruction.attachFamily"),
                H("attachFamily"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual family obtained by attaching the apex cone to the original subfamily."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("facets_mem"),
                DeclarationHandle.Create("D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWordConstruction.facets_mem"),
                H("facets_mem"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Membership in the facets-generated family agrees with the original downward-closed finite family."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pairedcone"),
                DeclarationHandle.Create("D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWordConstruction.pairedCone"),
                H("pairedCone"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The paired-cone Word contains the actual cone pairs and their original dependency order."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("attachword"),
                DeclarationHandle.Create("D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/CycleWordConstruction.attachWord"),
                H("attachWord"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual attachment Word combines the original old Word with its subfamily Word and proves partition, coverage and dependency order."))), DescribeRole.Definition))));
}
