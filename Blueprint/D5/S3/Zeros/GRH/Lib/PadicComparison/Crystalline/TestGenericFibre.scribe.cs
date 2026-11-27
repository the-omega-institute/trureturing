using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicComparison.Crystalline;

internal sealed class TestGenericFibreDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Test Generic Fibre", H("Test Generic Fibre"),
        Blocks(
            Paragraph(Text("Completed divided power envelope, its universal property, lifts from perfect rings and Witt vectors.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicComparison/Crystalline/TestGenericFibre.algebraMap_mem_pdIdeal"),
                H("algebraMap_mem_pdIdeal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a subset J of the S-algebra T and x in J, the image of x in the envelope E of T along J lies in 𝔡(E): n! divides its n-th power for every n.")))))));
}
