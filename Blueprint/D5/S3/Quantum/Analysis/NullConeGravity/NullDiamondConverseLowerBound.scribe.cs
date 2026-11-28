using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class NullDiamondConverseLowerBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondConverseLowerBound.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/satishchandransorce2026nulllocal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A lower bound for normalized covariance roots and divergence of their harmonic trace.",
        H("Covariance-root converse on null diamonds"),
        Blocks(
            Paragraph(Text("Equation (71) of Satishchandran and Sorce tests the trace of a squared root "
                + "difference. The operator estimate here controls the original perturbation by that "
                + "difference. A uniform lower bound for the radial perturbations then passes to the angular trace.")),
            Entry("normalizer", "covarianceNormalizer", "Covariance normalizer",
                "Take the ring inverse of the positive root of the normalization operator.", DescribeRole.Definition),
            Entry("root-difference", "covarianceRootDiff", "Normalized root difference",
                "Take positive roots after conjugating both covariances by the same inverse square root, "
                + "then subtract the reference root.", DescribeRole.Definition),
            Entry("perturbed-norm", "norm_B_prime_le_two", "Perturbed norm bound",
                "The order bound for the perturbed covariance is twice the normalization operator. "
                + "The congruence sends that upper bound to twice the identity."),
            Entry("reference-norm", "norm_A_prime_le_two_div_c", "Reference norm bound",
                "Coercivity bounds twice the identity above by two over the coercivity constant times "
                + "the normalization operator. Conjugating gives the same scalar bound on the reference norm."),
            Entry("difference-of-squares", "congruence_diff_eq", "Noncommutative difference of squares",
                "Place the perturbed root on the left of the root difference and the reference root on its right. "
                + "The cross terms cancel in their original order."),
            Entry("physical-converse", "hs_congruence_lower_bound", "Hilbert–Schmidt converse",
                "The ideal inequalities bound left and right multiplication by the respective operator norms. "
                + "Undoing the congruence costs the norm of the normalization operator. "
                + "The exact constant multiplies that norm by the sum of the square roots of two and two over coercivity."),
            Entry("sum-norm-converse", "hs_sum_norm_converse", "Common sum-norm converse",
                "Adding the identity to the normalizer raises the coercivity constant by one and "
                + "preserves domination of the perturbed covariance by twice the new normalizer."),
            Entry("non-hilbert-schmidt", "not_hs_sqrt_diff_of_not_hs_T", "Obstruction in one block",
                "A perturbation outside the Hilbert–Schmidt ideal forces the normalized root difference "
                + "outside that ideal."),
            Entry("two-sided-comparison", "quarterPower_block_comparison", "Two-sided block comparison",
                "A Hilbert–Schmidt quarter-power factor yields a finite upper estimate for each root difference. "
                + "The converse bounds the perturbation from this same normalized difference."),
            Entry("block-hypotheses", "ConverseBlockBounds", "Uniform block hypotheses",
                "The positive harmonic degrees share a lower coercivity constant, an upper normalizer norm, "
                + "the covariance order bounds, and a positive lower amplitude with the two angular factors.",
                DescribeRole.Definition),
            Entry("mode-weight", "converseModeWeight", "Harmonic trace contribution",
                "The contribution of a positive degree is its harmonic multiplicity times the squared "
                + "Hilbert–Schmidt norm of its normalized radial root difference.", DescribeRole.Definition),
            Entry("six-dimensional-growth", "converse_partial_trace_bounds_D6", "Six-dimensional cutoff",
                "For Hilbert–Schmidt radial root differences, the trace through degree L is bounded below "
                + "by a positive multiple of log L for L at least two."),
            Entry("higher-dimensional-growth", "converse_partial_trace_bounds_D_ge_7", "Higher-dimensional cutoff",
                "For Hilbert–Schmidt radial root differences, the trace through degree L is bounded below "
                + "by a positive multiple of L to the power D minus six."),
            Entry("trace-divergence", "converse_eq71_diverges_of_D_ge_6", "Divergence of the harmonic trace",
                "For D at least six the lower cutoff bounds tend to infinity. The individual "
                + "positive-degree trace contributions form a nonsummable sequence."),
            Entry("ambient-obstruction", "not_hs_eq71_operator_of_D_ge_6", "Block-diagonal operator obstruction",
                "If the ambient root difference were Hilbert–Schmidt, restricting its basis sum to "
                + "orthogonal copies of the radial modes would give a finite weighted sum. Positive "
                + "multiplicity makes each radial mode Hilbert–Schmidt, and the cutoff bounds contradict summability."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), role);
}
