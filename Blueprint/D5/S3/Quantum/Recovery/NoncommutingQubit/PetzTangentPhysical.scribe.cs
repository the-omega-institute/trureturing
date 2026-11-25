using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery.NoncommutingQubit;

internal sealed class PetzTangentPhysicalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The physical Petz residual entry is an arcsine average of the arithmetic BKM residual.",
        H("Physical qubit Petz tangent entries"),
        Blocks(Describe.Lean(
            DescribeId.Create("petztangentphysical-entry-arcsine-and-bound"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentPhysical.physical_entry_arcsine_and_bound"),
            H("Arcsine identity and quadratic bound for one spectral pair"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let Z be Hermitian on a retained qubit times a finite environment, and let H be an arbitrary complex matrix. " +
                    "The actual partial trace P of Z is positive definite. Choose joint and marginal unitary diagonalizations " +
                    "U and V, with joint eigenvalues λ and positive marginal eigenvalues p₀, p₁ summing to one. " +
                    "Select a joint pair i, j with λᵢ, λⱼ > 0 and set u = (λᵢ + λⱼ)/2, " +
                    "β = (λᵢ − λⱼ)/(λᵢ + λⱼ), g = sqrt(λᵢ λⱼ)/u and δ = 2 sqrt(p₀ p₁).")),
                Paragraph(Text(
                    "Let F(z) be the (i, j) entry of the native arithmetic BKM residual at (z + 1)/2 in the U basis. " +
                    "Let Y be the corresponding entry of H minus the actual square-root Petz sandwich of the partial trace of H. " +
                    "Then Y equals g times the arcsine average of F(z)/(1 − βz). " +
                    "Its squared modulus is at most K(δ) times the Lebesgue integral of |F(z)|²/(2(1 − βz)) on (−1, 1). " +
                    "Here K(1) = 1 and K(δ) = max(2, (3 − δ)/(1 + δ)) for 0 < δ < 1.")),
                Paragraph(Text(
                    "Expanding the marginal response in matrix units leaves the two opposite coherences in the same complex entry. " +
                    "The ordinary Petz sandwich replaces each affine marginal inverse by 1/sqrt(pₐ p_b), " +
                    "which is its arcsine average. The even and odd profiles use the two nodes 1 and δ, " +
                    "with the equal-node case included. The substitution t = z⁻² − 1 in the uniform energy " +
                    "produces the two integrals of the paired reciprocal Gram estimate."))),
            DescribeRole.Theorem))));
}
