using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.RealPlace;

internal sealed class SizeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Size", H("Size"),
        Blocks(
            Paragraph(Text("Size filtrations; size bounds for minors, heads and group elements near two frames. Q_j is Shape.Form.unitriGroup, 𝒩_{<j} is Shape.Form.unipotentBelow, w_p is weylElem.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/RealPlace/Size.hasMatSize_of_isHead"),
                H("hasMatSize_of_isHead"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let K consist of elements of size 1, j ≤ ϱ, s ∈ 𝒩_{<j}, sg ∈ K, and let Q_j w_p⁻¹g meet K. If p is a head, then g has size 60(ϱ+1)² and w_p⁻¹g has size 99(ϱ+1)².")))))));
}
