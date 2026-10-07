using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class CellLocalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Locality of the actual unbounded cellular colimit. These are new proofs over the official Mathlib pin and the protected defining maps. Released under the Apache 2.0 license.",
        H("Cell Locality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-celllocality-solidcellularcolimit-defect-acyclic"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/CellLocality.solidCellularColimit_defect_acyclic"),
                H("solid Cellular Colimit defect acyclic"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complete unbounded cellular colimit has zero locality defect."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-celllocality-solidcellularcolimit-homology-solid"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/CellLocality.solidCellularColimit_homology_solid"),
                H("solid Cellular Colimit homology solid"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cellular colimit is derived-local in every integer degree. This is locality of an actual construction, with no assumed replacement theorem."))),
                DescribeRole.Theorem))));
}
