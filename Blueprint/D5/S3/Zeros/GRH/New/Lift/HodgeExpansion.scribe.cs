using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Lift;

internal sealed class HodgeExpansionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hodge Expansion", H("Hodge Expansion"),
        Blocks(
            Paragraph(Text("Galois operators (g-1)/zτ deepen Kisin module elements at explicit cost in p. Exponent lattices: Frobenius shift, standard exponents give Frobenius pullbacks, exponents add under pairings.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Lift/HodgeExpansion.wittPairing_mem_withExponents"),
                H("wittPairing_mem_withExponents"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Exponents add: for an equivariant O-bilinear b: A × L → C, if y, x have exponents c', c at the letter i and c''_a(v) ≤ c'_a(u) + c_a(u') for allowed jumps with u + u' ≤ v, then b(y, x) has exponents c''.")))))));
}
