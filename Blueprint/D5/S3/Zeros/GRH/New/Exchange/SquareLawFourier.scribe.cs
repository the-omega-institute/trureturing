using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Exchange;

internal sealed class SquareLawFourierDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Square Law Fourier", H("Square Law Fourier"),
        Blocks(
            Paragraph(Text("Theta integrals under change to an isometric or opposite hermitian space. Finite-ring algebra of partner functions: shear identity and kernel with root-of-unity coefficients. Square identity for Fourier-transformed data over a finite ring, via matrix Gauss sums.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Exchange/SquareLawFourier.sum_fourier_eq_nextDatum"),
                H("sum_fourier_eq_nextDatum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For ψ, χ primitive, some γ with |γ|²|R|^{t(t+2n)} = 1 (n = #N, t = #T) has Σ_y 𝓕(p̄)(y)L′(y; 1₀) = γc·Σ_x 𝓕(conj p⁺)(x)L(1₀, x) for all p and c, L, L′ satisfying SquareLaw; 1₀ is the standard inclusion, p⁺ = nextDatum p.")))))));
}
