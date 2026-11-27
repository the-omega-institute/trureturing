using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Geometry;

internal sealed class ProperSchemesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Proper Schemes", H("Proper Schemes"),
        Blocks(
            Paragraph(Text("A proper scheme has closed diagonal and valuative lifting from one affine atlas.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Geometry/ProperSchemes.isProperOver_pointsToBase"),
                H("isProperOver_pointsToBase"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If s: X → Spec R is a proper morphism of schemes, then the functor of points of X over R is proper in the sense of IsProperOver.")))))));
}
