using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.Bruhat;

internal sealed class EichlerMapsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Eichler Maps", H("Eichler Maps"),
        Blocks(
            Paragraph(Text("Hermitian form, Eichler transformations are isometries; leading minors invariant under unitriangular groups.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/Bruhat/EichlerMaps.eichlerMap"),
                H("eichlerMap"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The matrix of the Eichler map v ↦ v + h(u, v)x − h(x, v)(u + ςx), where h is the form of J.")))))));
}
