using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.Construction;

internal sealed class PairDefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pair Defs", H("Pair Defs"),
        Blocks(
            Paragraph(Text("Space of data, Heisenberg and Weil operators, vacuum, theta functional, projections. Heisenberg law, unitarity, continuity, vacuum coefficients, theta product formula for the Weil representation. Space of maps between hermitian spaces, Weil action of the pair, theta kernel.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/Construction/PairDefs.hasSum_dataInner"),
                H("hasSum_dataInner"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For f, f' in 𝒮(V), the family ⟨f', ϱ(γ)f⟩, γ running over the rational vectors of V, is summable with sum θ(f) times the complex conjugate of θ(f').")))))));
}
