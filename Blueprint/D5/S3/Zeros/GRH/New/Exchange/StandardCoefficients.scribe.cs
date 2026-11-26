using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Exchange;

internal sealed class StandardCoefficientsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Standard Coefficients", H("Standard Coefficients"),
        Blocks(
            Paragraph(Text("If coefficients at unimodular indices vanish, all standard ramified data are killed.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Exchange/StandardCoefficients.apply_stdColDatum_eq_zero"),
                H("apply_stdColDatum_eq_zero"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Assume IsEquivariantLift for M, 𝒟, nested adapted splittings, the standard Ψ of the frame in M, and that ȷT-coefficients of 𝒟Ψ vanish on the parabolic for T = J_{V′} at unimodular lattices and for invertible T off the real class of V′. Then 𝒟 kills every standard datum of an integral z.")))))));
}
