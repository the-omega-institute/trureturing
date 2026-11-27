using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Geometry;

internal sealed class ProperAtlasDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Proper Atlas", H("Proper Atlas"),
        Blocks(
            Paragraph(Text("Smooth proper schemes are separated functors with finite étale atlases and affine covers.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Geometry/ProperAtlas.isAffinelyCovered_algPoints"),
                H("isAffinelyCovered_algPoints"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If every ring ι(c) satisfies IsComparableRing, the points of a proper R-scheme W on these rings are the restriction of a separated functor onto which the points of one affine scheme surject at every ι(c) (IsAffinelyCovered).")))))));
}
