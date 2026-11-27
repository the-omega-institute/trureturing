using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuColdSignedGibbsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuColdSignedGibbs.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The signed Gibbs map transports the odd kernel and determines its trace quartic.",
        H("The signed two-mode Gibbs calculation"),
        Blocks(
            Describe.Lean(DescribeId.Create("signed-map"), DeclarationHandle.Create(Owner + "signedMap"),
                H("Critical-time map"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Set u = s⁴, w = s³, M = 1 + s¹², L = 1 + w + w², h = (1 + u)/L and r = sh, where s = exp(−β/12) for inverse temperature β. The one-mode map multiplies coherences by √h and has population weights α = (s¹¹ + h)/M, η = w(1 − r)/M, ζ = u²(1 − r)/M and δ = (1 + s¹²r)/M. Apply the conjugation by diag(1, 1, −1, 1), the local map on the second mode, the same conjugation again, and the local map on the first mode."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("coherence-triangle"), DeclarationHandle.Create(Owner + "signedMap_triangle"),
                H("Action on the coherence triangle"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every s ≥ 0, let x be the 00-to-odd row, z the odd-to-11 column and d the 00-to-11 entry, all with arbitrary complex entries. In coordinate form let j(z) = (z₁, −z₀). The image has coordinates √h(αx + ηj(z)), √h(δz − ζj(x)) and hd, with the conjugate entries set by Hermiticity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("kernel-transport"), DeclarationHandle.Create(Owner + "signedMap_kernel"),
                H("Transport of the odd kernel direction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Write Nₐ(z) for the triangle with x = aj(z) and d = 0. For every s ≥ 0 and every complex z, the signed map sends Nᵤ(z) to √h N_w(z). The identities αu + η = w and ζu + δ = 1 give the two output coordinates."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pure-quartic"), DeclarationHandle.Create(Owner + "kernel_pure_quartic"),
                H("Exact quartic on the odd kernel direction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every s ≥ 0 and every complex z, set ν = |z₀|² + |z₁|² and Ω = diag(u², u, u, 1). The input contribution is 2/M² times the square of the real part of the ordinary trace of ΩNᵤ(z)². Subtracting the real part of the ordinary trace of the fourth power of the mapped direction gives 2h²w(2 + 3w + 2w²)ν²."))), DescribeRole.Theorem))));
}
