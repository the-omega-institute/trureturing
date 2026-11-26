using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuModularEdgeSpectralDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuModularEdgeSpectral.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Paired Gibbs jump energies in the spectral frame of a positive semidefinite density.",
        H("Spectral edges of paired Gibbs jumps"),
        Blocks(
            Describe.Lean(DescribeId.Create("generator-trace-eq-cosh"),
                DeclarationHandle.Create(Owner + "generatorTrace_eq_cosh"),
                H("Exact finite-family edge expansion"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Wu),
                Blocks(
                    Paragraph(Text("Let D be positive definite, let ρ be positive semidefinite, and take any real " +
                        "s > 1. Put p = 1/s, G = D^(p/2), M = ρ^p, and X = D^(−p/2) M D^(−p/2). " +
                        "For a finite family of jumps Jₖ, take positive rates aₖ, bₖ with " +
                        "D Jₖ D⁻¹ = (aₖ/bₖ) Jₖ. Use the generator " +
                        "L(X) = ∑ₖ [2aₖ K(Jₖ,X) + 2bₖ K(Jₖ*,X)], where " +
                        "K(V,X) = ((V*V)X + X(V*V))/2 − V*XV.")),
                    Paragraph(Text("If λᵢ are the eigenvalues of ρ and J̃ₖ is Jₖ in its orthonormal eigenframe, " +
                        "¼ Re Tr(M^(s−1) G L(X) G) equals ∑ₖᵢⱼ |(J̃ₖ)ᵢⱼ|² times the corresponding " +
                        "edge kernel, with u = bₖ λᵢ and v = aₖ λⱼ. For uv > 0 this kernel is " +
                        "√(uv) [cosh x − cosh(|2p−1| x)], where x = |log(u/v)|/2. " +
                        "For uv = 0 the kernel is (u + v)/2. This includes support crossings and " +
                        "assigns zero to entries with both endpoints outside the support.")),
                    Paragraph(Text("Moving the Gibbs powers through each jump scales its mixed term by " +
                        "(bₖ/aₖ)^p or (aₖ/bₖ)^p. The two projection terms contribute u + v, " +
                        "and the mixed terms contribute v^(1−p)u^p + u^(1−p)v^p, before division by two. " +
                        "Wu v1 (2.4) uses the conjugate exponent s' = s/(s−1). " +
                        "For the paired generator in (3.54), the physical energy is s s' = s²/(s−1) " +
                        "times the resulting edge sum. " +
                        "The weights, endpoints and support split are independent of s."))),
                DescribeRole.Theorem))));
}
