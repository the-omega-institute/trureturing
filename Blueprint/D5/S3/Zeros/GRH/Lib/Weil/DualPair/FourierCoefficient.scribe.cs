using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.DualPair;

internal sealed class FourierCoefficientDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fourier Coefficient", H("Fourier Coefficient"),
        Blocks(
            Paragraph(Text("Real mixed model of an adapted splitting; slices factor into real and finite parts. Mixed-model terms of a theta kernel: equivariance, moderate growth, integrability for onto data. Fourier coefficient of a theta lift as sum over frames, unfolded by Witt.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/DualPair/FourierCoefficient.centreCoeff_eq_integral_stabilizer"),
                H("centreCoeff_eq_integral_stabilizer"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Unfolding: let y be continuous, left Γ-invariant, satisfying Space.Splitting.HasIntegrableTerms, x₀ rational with invertible Gram matrix β, S the rational stabiliser of x₀. The x₀-term times y is S-invariant, integrable modulo S, with integral the Fourier coefficient at ȷβ and g of y's lift.")))))));
}
