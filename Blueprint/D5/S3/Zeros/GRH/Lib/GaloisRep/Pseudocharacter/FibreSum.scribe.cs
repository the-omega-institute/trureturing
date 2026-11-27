using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GaloisRep.Pseudocharacter;

internal sealed class FibreSumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fibre Sum", H("Fibre Sum"),
        Blocks(
            Paragraph(Text("Cancelling disjoint sets of characters from two semisimple representations with equal trace differences. Traces of powers determine eigenvalues and characteristic polynomials in characteristic zero. Functions obeying all trace identities are traces of semisimple representations. det(1 - cN) as product over eigenvalues. A vanishing finite sum descends along a map, weighted by fibre sizes.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GaloisRep/Pseudocharacter/FibreSum.exists_trace_limit"),
                H("exists_trace_limit"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Given IsApproximatingMonoid s c N and continuous r_x, suppose for each g a proper filter on N has first coordinate eventually in a complete L, second tending to (tr r_x(g))_x. Then (tr R(g), (tr r_x(g))_x) ∈ N for all g, some continuous semisimple R.")))))));
}
