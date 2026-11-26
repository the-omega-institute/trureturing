using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Core;

internal sealed class ModuleIndexDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Module Index", H("Module Index"),
        Blocks(
            Paragraph(Text("Index of a submodule bounded via determinants; multiplicativity; operators onto up to small index.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Core/ModuleIndex.of_det_dvd"),
                H("of_det_dvd"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let O be a valuation domain and A a square matrix over O indexed by ι whose determinant divides z. If N contains the image of A in O^ι, then IndexDvd holds for (O^ι, N, z).")))))));
}
