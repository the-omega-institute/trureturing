using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.CausalMoments;

internal sealed class NonfairMediationEnclosureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/CausalMoments/NonfairMediationEnclosure.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite rational nonfair outcome transport on the original complete-mediation model.",
        H("NonfairMediationEnclosure"),
        Blocks(
            Paragraph(Text("All theorem entries are bound to their Lean declarations without formula projection. The original mediator and outcome probability-law semantics are retained. No compilation or independent review status is asserted by this source document.")),
            Describe.Lean(DescribeId.Create("kernelbenefitvalues"),
                DeclarationHandle.Create(Prefix + "kernelBenefitValues"), H("Original attainable values at a given kernel"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both independent mechanism laws range subject to the original mediator marginals, complete-mediation equations and all target outcome means."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("transfer-kernel-upper-bound"),
                DeclarationHandle.Create(Prefix + "transfer_kernel_upper_bound"), H("Propagate a valid global bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Reverse outcome transports carry any valid source-kernel bound to a bound on the entire target-kernel family."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("attained-kernel-optima-stability"),
                DeclarationHandle.Create(Prefix + "attained_kernel_optima_stability"), H("Compare two attained optima"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual greatest-value premises give the signed optimum stability formula. This corollary does not assert general optimizer existence; the principal enclosure below supplies a feasible law unconditionally."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("partition-anchor-upper"),
                DeclarationHandle.Create(Prefix + "partition_anchor_upper"), H("The fair anchor is an upper envelope after centering"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an optimal original marginal partition, its half-score plus the exact drift bounds every nonfair model. No positive radius is added on this side."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nonfair-kernel-global-enclosure"),
                DeclarationHandle.Create(Prefix + "nonfair_kernel_global_enclosure"), H("Construct a feasible nonfair model and a global bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing fair partition theorem supplies an anchor and original mediator coupling. Transporting only its outcome disturbance constructs a target-kernel law within one radius of the globally valid upper envelope. No nonfair optimizer is assumed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sensitivityweight-bounds"),
                DeclarationHandle.Create(Prefix + "sensitivityWeight_bounds"), H("Nonnegative improved weights"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The off-diagonal weight lies between zero and the older combined-marginal weight."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("kernelradius-le-uniform-error"),
                DeclarationHandle.Create(Prefix + "kernelRadius_le_uniform_error"), H("No dimension multiplier for uniform errors"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A common coordinate error bound epsilon yields radius at most epsilon, using total combined mediator mass two."))), DescribeRole.Theorem))));
}
