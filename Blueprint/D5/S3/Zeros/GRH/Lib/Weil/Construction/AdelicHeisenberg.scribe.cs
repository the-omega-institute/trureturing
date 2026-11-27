using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.Construction;

internal sealed class AdelicHeisenbergDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adelic Heisenberg", H("Adelic Heisenberg"),
        Blocks(
            Paragraph(Text("Adelic vacuum function and Heisenberg cocycle of the standard hermitian form.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/Construction/AdelicHeisenberg.adelicHeis"),
                H("adelicHeis"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The Heisenberg datum on adelic n-space with bicharacter β(x,y)=ψ(½ȷ h(y,x)), h being the standard hermitian form of signs s.")))))));
}
