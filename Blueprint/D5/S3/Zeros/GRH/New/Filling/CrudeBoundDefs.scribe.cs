using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Filling;

internal sealed class CrudeBoundDefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Crude Bound Defs", H("Crude Bound Defs"),
        Blocks(
            Paragraph(Text("Chinese remainder lift at level primes; fixers of frame vectors modulo them. Levels, normal forms, cells, near and congruent terms, boxes and size parameters.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Filling/CrudeBoundDefs.CharsAgree"),
                H("CharsAgree"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The finite character Filling.unipotentChar takes the same value at u and at γ⁻¹uγ for every rational u in 𝖴 ∩ γ𝖴γ⁻¹.")))))));
}
