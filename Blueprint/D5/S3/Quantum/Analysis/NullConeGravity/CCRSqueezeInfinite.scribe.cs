using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class CCRSqueezeInfiniteDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeInfinite.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/satishchandransorce2026nulllocal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The norm limit of finite squeeze products and the resulting diagonal Gaussian vector state.",
        H("Square-summable squeezes in Fock space"),
        Blocks(
            Paragraph(Text("This construction represents the diagonal Gaussian covariance by a unit "
                + "vector in the reference Fock space, as needed in the Gaussian excitability "
                + "problem of Satishchandran and Sorce. The finite subsets of any basis index type "
                + "form the directed set for the norm limit.")),
            Entry("finite-squeeze", "finiteSqueeze", "Finite squeeze product",
                "Use a one-mode squeezed vector at each selected mode and the vacuum at each "
                + "unselected mode.", DescribeRole.Definition),
            Entry("finite-squeeze-coordinate", "finiteSqueeze_apply", "Finite squeeze amplitudes",
                "If an occupation is supported on the selected modes, its amplitude is the product "
                + "of their one-mode amplitudes. Otherwise its amplitude is zero."),
            Entry("finite-squeeze-norm", "finiteSqueeze_norm", "Norm of a finite squeeze product",
                "The occupation sum factors into the one-mode squared norms, all equal to one."),
            Entry("finite-squeeze-overlap", "finiteSqueeze_inner", "Overlap for nested finite sets",
                "For F contained in G, the overlap is the product of 1/√cosh(r) over G outside F. "
                + "Modes in F contribute their squared norms."),
            Entry("finite-squeeze-distance", "finiteSqueeze_sub_norm_sq_le", "Squared distance for nested finite sets",
                "The squared distance is at most one half of the sum of r² over the added modes. "
                + "The bound cosh(r) ≤ exp(r²/2) controls the overlap, and 1 − t ≤ exp(−t) "
                + "converts that control into the distance estimate."),
            Entry("finite-squeeze-cauchy", "finiteSqueeze_cauchy", "Cauchy net of finite squeeze products",
                "Square summability controls the tail over added modes. For two finite sets above "
                + "a common cutoff, apply the nested-set estimate through their union."),
            Entry("infinite-squeeze", "infiniteSqueeze", "Infinite squeeze vector",
                "Take the norm limit of the finite squeeze products.", DescribeRole.Definition),
            Entry("finite-squeeze-limit", "finiteSqueeze_tendsto", "Norm convergence of the finite products",
                "Completeness gives convergence of the finite squeeze products to the infinite squeeze vector."),
            Entry("infinite-squeeze-norm", "infiniteSqueeze_norm", "Norm of the infinite squeeze vector",
                "The norm is one by continuity of the norm along the finite products."),
            Entry("infinite-squeeze-weyl", "infiniteSqueeze_weyl_inner", "Infinite-mode Weyl expectation",
                "Project the displacement parameter onto the same finite sets. Its Weyl expectation "
                + "in each finite product factors into the one-mode expectations. The projected "
                + "parameters and the finite vectors converge in norm. Strong continuity and the "
                + "isometry bound give the limit on the Weyl side. On the covariance side, bounded "
                + "exponential weights dominate the series by the squared Hilbert coordinates."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), role);
}
