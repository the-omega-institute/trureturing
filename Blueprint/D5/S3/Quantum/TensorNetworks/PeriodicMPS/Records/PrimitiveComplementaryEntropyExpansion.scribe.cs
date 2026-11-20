using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Records;

internal sealed class PrimitiveComplementaryEntropyExpansionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveComplementaryEntropyExpansion";
    private const string Title = "Complementary conditional entropy of the primitive periodic collision";
    private static LibraryNoteRef EntropySource => LibraryNoteRef.Create("D5/L/Quantum/watrous2018entropicidentities");
    private static LibraryNoteRef CollisionSource => LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title + ".", H(Title),
        Blocks(
            Claim("matrixEntropy", "Spectral entropy in nats",
                "The repository function sums −x log x over the real parts of the characteristic "
                + "roots with multiplicities. On a density matrix these are its eigenvalues. "
                + "The logarithm is natural and a zero eigenvalue contributes zero.",
                AssessedProvenance.FromRepo(EntropySource), DescribeRole.Definition),
            Claim("matrixEntropy_eq_density", "Agreement with trace-log entropy",
                "For every finite density state the spectral sum agrees with the finite-state "
                + "von Neumann entropy −Re tr(P log P), including singular P.",
                AssessedProvenance.FromRepo(EntropySource)),
            Claim("collisionComplementaryEntropy", "The literal complementary conditional entropy",
                "Let m count the hidden sites and let n = 2 + m. The normalized amplitude "
                + "flattening Wᵦ has rows on the first two sites and columns on the last m sites. "
                + "The literal complementary density is Eᵦ = (Wᵦ†Wᵦ)ᵀ in the amplitude basis. "
                + "For m ≥ 5 the fair classical–quantum state has diagonal blocks E₀/2 and E₁/2. "
                + "Conditioning the label B on the last m sites gives H(B|E) = S(BE) − S(E), "
                + "where the environment marginal is (E₀ + E₁)/2.",
                AssessedProvenance.FromRepo(CollisionSource, EntropySource), DescribeRole.Definition),
            Claim("collisionGram", "The eight-dimensional block Gram",
                "With R the common two-site density, G(Z) is half the block matrix with R "
                + "on both diagonals, Z in the upper-right block and Z† in the lower-left block.",
                AssessedProvenance.FromRepo(CollisionSource), DescribeRole.Definition),
            Claim("collisionComplementaryEntropy_eq_gram", "Exact reduction to two block Grams",
                "For every m ≥ 5, H(B|E) = S(G(0)) − S(G(Sₙ)), where Sₙ = W₀W₁† "
                + "in the ket-first convention. Rectangular Gram matrices share their nonzero "
                + "eigenvalues with multiplicity, and transpose preserves the characteristic roots.",
                AssessedProvenance.FromRepo(CollisionSource, EntropySource)),
            Claim("collision_cross_exponential_remainder", "Uniform bound on the subdominant cross entries",
                "One nonnegative constant C bounds every visible entry of Sₙ − γⁿS★ by Cβⁿ "
                + "in absolute value, where γ = (1+i)(3+√41)/√200, S★ is the exact leading matrix, "
                + "β = 8/√200 and n = 2 + m.",
                AssessedProvenance.FromRepo(CollisionSource)),
            Claim("collisionBeta_lt_alpha_sq", "The subdominant rate lies below the entropy scale",
                "The rate β is strictly smaller than α², where α = |γ| = (3+√41)/10.",
                AssessedProvenance.FromRepo(CollisionSource)),
            Claim("collision_entropy_replacement_bound", "Entropy error from replacing the actual cross block",
                "For all sufficiently large m the absolute difference between S(G(Sₙ)) and "
                + "S(G(αⁿS★)) is at most Kβⁿ for a nonnegative constant K. The phase of γⁿ "
                + "is removed by block-unitary conjugation. A local eigenvalue perturbation "
                + "bound at the positive definite G(0) controls the entropy difference.",
                AssessedProvenance.FromRepo(CollisionSource, EntropySource)),
            Claim("collision_commuting_entropy_quadratic", "Quadratic entropy of the leading Gram path",
                "As real t tends to zero through nonzero values, [S(G(0)) − S(G(tS★))]/t² "
                + "tends to (310625−46875√41)/16384. The Hermitian slope commutes with G(0), "
                + "so the path reduces to scalar expansions of −x log x.",
                AssessedProvenance.FromRepo(CollisionSource, EntropySource)),
            Claim("collision_complementary_entropy_asymptotic", "Exact coefficient of the complementary conditional entropy",
                "For the fair label conditioned on the literal complementary partial trace, "
                + "H(B|E)/α^(2n) tends to (310625−46875√41)/16384 as m tends to infinity, "
                + "with n = 2 + m. The coefficient uses natural-log entropy.",
                AssessedProvenance.FromRepo(CollisionSource, EntropySource)))));

    private static DocumentBlock Claim(string name, string title, string prose,
        AssessedProvenance provenance, DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("primitive-complementary-entropy-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            provenance, Blocks(Paragraph(Text(prose))), role);
}
