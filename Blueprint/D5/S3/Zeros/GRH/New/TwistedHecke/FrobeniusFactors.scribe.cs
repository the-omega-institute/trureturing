using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.TwistedHecke;

internal sealed class FrobeniusFactorsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Frobenius Factors", H("Frobenius Factors"),
        Blocks(
            Paragraph(Text("Frobenius-power products of generic matrices: monomial weights track the excess up to error.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/TwistedHecke/FrobeniusFactors.pow_dvd_coeff_conj_frobOperator"),
                H("pow_dvd_coeff_conj_frobOperator"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let a' = a+1, Nnk(ℓ+2) ≤ P^ℓ, ℓ ≤ N, and, for j = s − d and e = P^d, ψ(s,d) = ι_s(h)(ι_j(h)⁻¹g_jι_j(h))^{(e)}ι_s(h)⁻¹ (entrywise powers). In row β of TwistingData.frobOperator, w^c divides the coefficient of ν if ν_j has equal row and column TwistingData.indexWeight-weights for j ≠ i and |excess of β at i+ℓ − row weight of ν_i| > 2c+1.")))))));
}
