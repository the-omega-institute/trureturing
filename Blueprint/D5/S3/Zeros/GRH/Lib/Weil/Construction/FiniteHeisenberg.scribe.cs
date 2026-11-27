using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.Construction;

internal sealed class FiniteHeisenbergDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Heisenberg", H("Finite Heisenberg"),
        Blocks(
            Paragraph(Text("Finite adelic Heisenberg group, self-dual lattice, additive character, semicharacter and vacuum.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/Construction/FiniteHeisenberg.traceOneAdele_add_star"),
                H("traceOneAdele_add_star"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The element c₀ of the Weil data, viewed as a finite adele, satisfies c₀ + c̄₀ = 1.")))))));
}
