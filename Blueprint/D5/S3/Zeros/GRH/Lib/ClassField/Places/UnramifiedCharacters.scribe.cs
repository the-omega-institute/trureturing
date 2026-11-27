using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.Places;

internal sealed class UnramifiedCharactersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unramified Characters", H("Unramified Characters"),
        Blocks(
            Paragraph(Text("Prime induced by a p-adic embedding; extension to the completion and finite adeles. Unique unramified character with given value at Frobenius; uniform local constancy.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/Places/UnramifiedCharacters.existsUnique_unramified_char"),
                H("existsUnique_unramified_char"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let Γ be the absolute Galois group of a local field k and φ an arithmetic Frobenius. For every r in ℚ/ℤ there is exactly one continuous character χ : Γ → ℚ/ℤ that is trivial on inertia and has χ(φ) = r.")))))));
}
