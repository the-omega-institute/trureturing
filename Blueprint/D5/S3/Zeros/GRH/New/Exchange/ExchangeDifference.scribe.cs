using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Exchange;

internal sealed class ExchangeDifferenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exchange Difference", H("Exchange Difference"),
        Blocks(
            Paragraph(Text("Difference of both theta integrals is an equivariant functional of one partner datum.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Exchange/ExchangeDifference.exists_isEquivariantLift"),
                H("exists_isEquivariantLift"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For W of even rank, rapid v, v′ and c ∈ ℂ, there are a space M of data and a linear 𝒟 satisfying IsEquivariantLift such that for integral partners Φ, Ψ with Ψ locally constant, Ψ ∈ M and 𝒟Ψ = thetaLarge Φ − c·thetaSmall Ψ.")))))));
}
