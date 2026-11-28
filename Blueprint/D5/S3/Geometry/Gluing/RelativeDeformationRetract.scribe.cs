using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class RelativeDeformationRetractDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strong deformation retractions onto finite subcomplexes",
        H("Strong deformation retractions onto finite subcomplexes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("strong-deformation-retract-from-subcomplex-homotopy-equivalence"),
                DeclarationHandle.Create("D5/S3/Geometry/Gluing/RelativeDeformationRetract.strongDeformationRetract_of_homotopyEquiv"),
                H("A homotopy-equivalent subcomplex inclusion yields a strong deformation retraction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
                Blocks(Paragraph(Text("Homotopy extension first turns a homotopy inverse of the realization inclusion into a strict retraction. A second extension, into the compact-open path space, cancels the out-and-back homotopy on the subcomplex. The resulting deformation fixes every point of the subcomplex."))),
                DescribeRole.Theorem))));
}
