using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HilbertOperators;

internal sealed class TwoStepDefectComparisonDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/HilbertOperators/TwoStepDefectComparison.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two retractions onto one visible subspace give a factored difference of compression defects.",
        H("Two-step compression defect comparison"),
        Blocks(
            Entry("two-step-defect", "twoStepDefect", "Two-step defect",
                "For a bounded T and inclusion i of V, the defect of R is R T² i minus (R T i)².",
                DescribeRole.Definition),
            Entry("defect-difference", "defect_sub_eq", "Hidden-block factorization",
                "For a retraction R onto V and the orthogonal projection P onto V, the defect difference " +
                "equals (K W − E K) C. Here K is R restricted to the orthogonal complement, W is the " +
                "hidden block of T, E is R T i, and C is the visible-to-hidden block of T. " +
                "Splitting T on each return from the hidden subspace gives the identity."),
            Entry("centered-bound", "norm_defect_sub_le", "Centered block estimate",
                "Subtracting the same complex scalar times the identity from W and E leaves K W − E K " +
                "unchanged. The norm bound uses the sum of the two centered block norms, multiplied " +
                "by the norms of K and C."),
            Entry("relative-bound", "norm_defect_sub_le_relative", "Relative metric estimate",
                "If R is orthogonal for a symmetric coefficient between l I and u I, its hidden " +
                "restriction has norm at most (u − l)/(2√(ul)) for 0 < l ≤ u. Insertion into the " +
                "centered block estimate bounds the defect difference in the reference operator norm."),
            Entry("double-time-identity", "exponential_defect_sub_eq", "Double-time factorization",
                "For T = exp(t L) and any real t, the operator exponential law identifies T² with " +
                "exp(2t L) and gives the same hidden-block factorization."),
            Entry("quadratic-bound", "norm_defect_sub_le_sq", "Bound by the centered evolution",
                "Both centered blocks and the visible-to-hidden block are controlled by T − c I. " +
                "The resulting defect bound is ||K|| (1 + ||R||) ||T − c I||²."),
            Entry("small-time-order", "exponential_defect_sub_isBigO", "Quadratic small-time order",
                "A bounded complex-linear generator gives an exponential displacement of order |t| near " +
                "zero. The difference of the two compression defects is therefore O(t²)."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string prose,
        DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
