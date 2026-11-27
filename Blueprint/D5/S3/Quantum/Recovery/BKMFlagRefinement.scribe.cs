using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class BKMFlagRefinementDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Recovery/BKMFlagRefinement.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive normalized refinements of classical flags preserve the actual marginal and physical BKM defects.",
        H("Physical BKM defects under classical flag refinement"),
        Blocks(
            Entry("refined-blocks", "refinedBlocks", "Refined reference",
                "Use a finite child set for each parent flag. Its child blocks are the parent block " +
                "multiplied by the corresponding weights. The joint reference acts on retained " +
                "space tensored with the flag space.", DescribeRole.Definition),
            Entry("actual-marginal", "marginal_refined", "Preservation of the actual marginal",
                "Taking the right partial trace gives the sum of the blocks. When each parent's weights " +
                "sum to one, summing its child blocks recovers the parent, so the old and new right " +
                "partial traces agree."),
            Entry("log-defect", "logDefect", "Logarithmic commutator defect",
                "Subtract the identity lift of the marginal logarithm from the joint logarithm, then " +
                "commute with the identity lift of the retained observable. The defect is the real " +
                "trace of the joint reference times the squared absolute value of that commutator.",
                DescribeRole.Definition),
            Entry("bkm-gap", "bkmGap", "BKM metric gap",
                "Subtract the joint BKM quadratic form of the lifted observable from the marginal BKM " +
                "quadratic form of the retained observable. Both forms use the integral of the left " +
                "and right matrix powers with exponents adding to one.", DescribeRole.Definition),
            Entry("defect-equalities", "refine_defects", "Exact invariance of both defects",
                "For every positive definite block family, every positive normalized refinement and " +
                "every retained matrix, the logarithmic defect and BKM gap agree before and after " +
                "refinement. A positive scalar adds a scalar identity to a block logarithm, so the " +
                "commutator is unchanged. The block trace term scales by the child weight. In the BKM " +
                "integral the two powers contribute scalar factors whose exponents sum to one. " +
                "Summing the child contributions thus restores both original block sums."),
            Entry("physical-refinement", "physical_refinement", "Faithful normalization and physical defects",
                "Assume a nonempty parent flag set, positive definite parent blocks whose joint trace " +
                "is one, positive weights summing to one at each parent and a Hermitian retained " +
                "observable. Both joint references are positive definite and the refined joint trace " +
                "is one. The original marginal is positive definite with trace one and equals the " +
                "refined marginal. Both identity lifts are Hermitian and the physical defects agree."),
            Entry("positive-gap-ratio", "refine_positive_gap_and_ratio", "Positive gap and defect ratio",
                "If the original BKM gap is strictly positive, the refined gap is strictly positive " +
                "and the ratio of the logarithmic defect to the BKM gap is equal before and after " +
                "refinement."),
            Entry("uniform-refinement", "uniform_refinement", "Uniform splitting of one flag",
                "Split a chosen parent into a positive number of equal-weight children and give " +
                "each other parent one child of weight one. The actual marginal and both defects " +
                "are preserved."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string prose,
        DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
