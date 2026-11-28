using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class NullDiamondKernel5DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernel5D.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/satishchandransorce2026nulllocal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The elementary five-dimensional null-diamond kernel and its weighted Hilbert–Schmidt factorization.",
        H("Five-dimensional modular correction"),
        Blocks(
            Entry("mixed-radial-derivative", "correction5D_mixed_deriv", "Elementary boundary correction",
                "For positive radii and angular dot product below one, differentiate the scaled "
                + "half-integer bulk difference in each radius. The two derivatives give the "
                + "exponential times the linear factor in Appendix A."),
            Entry("real-modular-kernel", "kernelG5D_ofReal", "Real modular kernel",
                "On the real axes the holomorphic kernel equals the boundary correction at "
                + "the two logistic radii times both logistic Jacobians and the covariance factor four."),
            Entry("closed-strip-root-bound", "modularRoot_closedStrip_bound", "Bounds on the modular roots",
                "On the closed strip of width 3/8, each root has modulus at most the reciprocal "
                + "of the square root of cos(3π/8). The real part of their product is bounded "
                + "below by the negative of that modulus bound squared."),
            Entry("strip-fourier-decay", "fourierG5D_bound", "Exponential Fourier decay",
                "For each positive mass, the two-frequency kernel is bounded by a mass-dependent "
                + "constant times the product of two exponentials of rate 3/8 and the inverse "
                + "square root of one minus the angular dot product. The separate modular roots "
                + "avoid the principal branch cut. Horizontal contour shifts give the two "
                + "exponential factors."),
            Entry("phase-measure", "phase5DMeasure", "Phase measure",
                "Use Lebesgue measure in frequency and round measure on the celestial three-sphere.",
                DescribeRole.Definition),
            Entry("normalized-kernel", "tKernel5D", "Normalized kernel",
                "Evaluate the two-frequency kernel at the angular dot product and divide by the "
                + "product of the square roots of the radial normalization weights.", DescribeRole.Definition),
            Entry("weighted-kernel", "wKernel5D", "Inverse quarter weights",
                "Multiply the normalized kernel by the inverse quarter power of the positive "
                + "symbol in each frequency.", DescribeRole.Definition),
            Entry("weighted-integrability", "wKernel5D_memLp", "Weighted square integrability",
                "The inverse powers use at most 1/4 of the decay rate in each frequency, leaving "
                + "rate 1/8. The angular square has finite integral on the product of round spheres."),
            Entry("massless-operator", "nullA5D", "Massless multiplier",
                "The bounded operator A multiplies by 2/(1 + exp(ν)).", DescribeRole.Definition),
            Entry("centered-operator", "nullJ5D", "Centered multiplier",
                "The bounded operator J equals A minus the identity.", DescribeRole.Definition),
            Entry("weighted-operator", "nullW5D", "Weighted integral operator",
                "The operator W is realized by the inverse-quarter-weighted kernel.", DescribeRole.Definition),
            Entry("correction-operator", "nullT5D", "Massive correction operator",
                "The operator T is realized by the normalized correction kernel.", DescribeRole.Definition),
            Entry("weighted-hilbert-schmidt", "nullW5D_hs", "Hilbert–Schmidt weighted operator",
                "The operator W is Hilbert–Schmidt by the square-integrable kernel theorem."),
            Entry("correction-hilbert-schmidt", "nullT5D_hs", "Hilbert–Schmidt massive correction",
                "The operator T is Hilbert–Schmidt by square integrability of the normalized kernel."),
            Entry("massless-positivity", "nullA5D_nonneg", "Nonnegative massless operator",
                "The quadratic form of A integrates the positive frequency symbol against "
                + "the squared modulus of the input."),
            Entry("centered-kernel", "nullJ5D_ker", "Trivial kernel of the centered multiplier",
                "The symbol of J vanishes on the phase-space slice of frequency zero, which has "
                + "measure zero. Thus J has trivial kernel."),
            Entry("correction-self-adjoint", "nullT5D_selfAdjoint", "Self-adjoint massive correction",
                "Reality and exchange symmetry of the modular kernel give a Hermitian Fourier "
                + "kernel by Fubini. The angular dot product and normalization are symmetric."),
            Entry("quarter-power-factorization", "nullT5D_factor", "Quarter-power factorization",
                "The positive fourth root of A is the pointwise quarter-power multiplier. "
                + "Applying it on both sides of W cancels the two inverse weights and gives T."),
            Entry("frequency-conjugation", "nullConj5D", "Frequency conjugation",
                "Reverse the frequency and conjugate pointwise to obtain an isometric, "
                + "conjugate-linear involution.", DescribeRole.Definition),
            Entry("conjugation-representative", "nullConj5D_ae", "Almost-everywhere action",
                "A representative of the conjugated vector agrees almost everywhere with "
                + "the complex conjugate evaluated at the negated frequency and original direction."),
            Entry("conjugation-commutes", "nullConj5D_comm_T", "Commutation with the massive correction",
                "Reflecting both frequencies conjugates the normalized Fourier kernel and "
                + "preserves phase measure, so frequency conjugation commutes with T."),
            Entry("conjugation-anticommutes", "nullConj5D_anti_J", "Anticommutation with the centered multiplier",
                "The real symbol of J is odd, so frequency conjugation anticommutes with J."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), role);
}
