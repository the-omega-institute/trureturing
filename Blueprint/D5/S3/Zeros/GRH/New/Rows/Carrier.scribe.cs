using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Rows;

internal sealed class CarrierDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Carrier", H("Carrier"),
        Blocks(
            Paragraph(Text("Matched identity summed on a square block; datum reduces to one coset's class sum. Exchange of theta kernels with explicit determinant polynomials and Hecke L-value constant. Twisted theta class sums equal Hecke-value multiples of a constant and of the carrier.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Rows/Carrier.stdClassSum_carrierXi_eq_carrierForm"),
                H("stdClassSum_carrierXi_eq_carrierForm"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let m > 0 be even. For some C, every c of weight 0, tame for (𝔪, χ), has γ with |γ|² = C/(nL(cυ^{m/2}, m/2)·nL(c⁻¹υ^m, m)) and γ·Σ_h carrierXi(h)·θ_{υ^m,c}[χ∘det, 1](x, h) = carrierForm(x) for all x; nL = lValueProd at the places of 𝔪.")))))));
}
