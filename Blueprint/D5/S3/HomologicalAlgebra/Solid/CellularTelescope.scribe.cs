using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class CellularTelescopeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual mapping telescope of the saved unbounded cellular sequence. Its derived universal comparison is proved against all derived-local targets. A quasi-isomorphism to the ordinary cellular colimit and realization in D(Solid) remain separate obligations. New proofs, Apache 2.0.",
        H("Cellular Telescope"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-cellulartelescope-solidcellulartelescope-derivedprecomp-bijective"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/CellularTelescope.solidCellularTelescope_derivedPrecomp_bijective"),
                H("solid Cellular Telescope derived Precomp bijective"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The saved sequence's actual mapping telescope has a universal derived comparison to every derived-local object: existence and uniqueness hold for all roofs and for arbitrary unbounded starting complexes."))),
                DescribeRole.Theorem))));
}
