using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class NullDiamondMultipliers4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/satishchandransorce2026nulllocal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Square-integrable weighted kernels and frequency conjugation on the four-dimensional null diamond.",
        H("Weighted kernel factorization and conjugation"),
        Blocks(
            Paragraph(Text("The phase space carries Lebesgue frequency measure and round angular measure. "
                + "The massive correction acts by an integral kernel on complex square-integrable functions. "
                + "The massless part acts by a bounded real frequency multiplier.")),
            Entry("frequency-weight", "wgt", "Radial normalization",
                "At real frequency ν the weight is ν cosh(ν/2) divided by sinh(ν/2), with value 2 at zero.",
                DescribeRole.Definition),
            Entry("massless-symbol", "a", "Positive symbol",
                "The real multiplier at frequency ν is 2/(1 + exp(ν)).", DescribeRole.Definition),
            Entry("centered-symbol", "freqJ", "Centered symbol",
                "The centered symbol is the positive symbol minus one.", DescribeRole.Definition),
            Entry("weight-bounds", "wgt_bounds", "Bounds on the radial normalization",
                "For every real ν the weight is at least 2 and at least |ν|, and at most 2 + |ν|."),
            Entry("correction-kernel", "tKernel", "Normalized massive correction",
                "Evaluate the two-frequency Fourier kernel at the angular dot product and divide by "
                + "the product of the square roots of the two radial weights.", DescribeRole.Definition),
            Entry("weighted-kernel", "wKernel", "Inverse quarter weights",
                "Multiply the normalized kernel by the inverse quarter powers of the positive symbol "
                + "in the two frequency variables.", DescribeRole.Definition),
            Entry("weighted-integrability", "wKernel_memLp", "Weighted square integrability",
                "For every positive mass the weighted kernel is in L² of the product phase measure. "
                + "The strip decay of rate 3/8 absorbs growth of rate 1/4 in each variable. "
                + "The squared majorant separates into two integrable radial exponentials of rate 1/4 "
                + "and an integrable squared angular logarithm."),
            Entry("massless-operator", "nullA", "Massless multiplier operator",
                "The bounded operator A multiplies by the positive symbol.", DescribeRole.Definition),
            Entry("centered-operator", "nullJ", "Centered multiplier operator",
                "The bounded operator J equals A minus the identity.", DescribeRole.Definition),
            Entry("weighted-operator", "nullW", "Weighted integral operator",
                "For each positive mass W is the integral operator with the inverse-quarter-weighted kernel.",
                DescribeRole.Definition),
            Entry("correction-operator", "nullT", "Massive integral operator",
                "For each positive mass T is the integral operator with the normalized correction kernel.",
                DescribeRole.Definition),
            Entry("weighted-hilbert-schmidt", "nullW_hs", "Hilbert–Schmidt weighted operator",
                "For every positive mass W is Hilbert–Schmidt by the square-integrable kernel realization."),
            Entry("correction-hilbert-schmidt", "nullT_hs", "Hilbert–Schmidt massive correction",
                "For every positive mass T is Hilbert–Schmidt. Its kernel has the full contour decay rate."),
            Entry("massless-positivity", "nullA_nonneg", "Massless positivity",
                "The operator A is nonnegative because its quadratic form integrates the positive symbol "
                + "against the squared modulus of the input."),
            Entry("quarter-power-factorization", "nullT_factor", "Quarter-power factorization",
                "For every positive mass T equals A to the quarter power times W times A to the quarter power. "
                + "Two applications of uniqueness of the positive square root identify the fourth root with "
                + "the pointwise quarter-power multiplier. Its two symbol factors cancel the inverse weights."),
            Entry("correction-self-adjoint", "nullT_selfAdjoint", "Self-adjoint massive correction",
                "For every positive mass T is self-adjoint. Reality and exchange symmetry of the position "
                + "kernel give a Hermitian Fourier kernel by Fubini."),
            Entry("centered-kernel", "nullJ_ker", "Trivial kernel of the centered multiplier",
                "The kernel of J is the zero submodule. Its symbol can vanish only on the phase-space "
                + "slice with frequency zero, which has measure zero."),
            Entry("frequency-conjugation", "nullConj", "Frequency conjugation",
                "Conjugation after reversal of the frequency defines a real-linear isometric equivalence "
                + "of the phase Hilbert space.", DescribeRole.Definition),
            Entry("conjugation-representative", "nullConj_ae", "Almost-everywhere action",
                "For every input the output agrees almost everywhere with the complex conjugate of the "
                + "input evaluated at the negated frequency and the original angular direction."),
            Entry("conjugation-scalar", "nullConj_smul", "Conjugate linearity",
                "For every input and complex scalar, conjugating the scalar multiple multiplies the "
                + "conjugated input by the conjugate of the scalar."),
            Entry("conjugation-involution", "nullConj_involutive", "Involution",
                "Applying frequency conjugation twice gives the original input."),
            Entry("conjugation-commutes", "nullConj_comm_T", "Commutation with the massive correction",
                "For every positive mass and input, frequency conjugation commutes with T. Reflection of "
                + "both frequencies conjugates the Fourier kernel and preserves the frequency measure."),
            Entry("conjugation-anticommutes", "nullConj_anti_J", "Anticommutation with the centered multiplier",
                "For every input frequency conjugation sends J applied to the input to minus J applied "
                + "to the conjugated input, because the centered frequency symbol is odd."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), role);
}
