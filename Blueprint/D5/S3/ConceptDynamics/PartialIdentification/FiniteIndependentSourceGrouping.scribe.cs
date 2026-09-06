using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.PartialIdentification;

internal sealed class FiniteIndependentSourceGroupingDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/PartialIdentification/FiniteIndependentSourceGrouping.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent elementary disturbance laws induce one partition-independent full source law. Regrouping and local query elimination preserve that law exactly.",
        H("Finite independent source grouping"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("independent-source-law"),
                DeclarationHandle.Create(Prefix + "independentSourceLaw"),
                H("Full independent source law"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The product of elementary rational masses is nonnegative and normalized by the pinned finite product-of-sums theorem. Noise carriers may depend on the source index."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("independent-source-mass-split"),
                DeclarationHandle.Create(Prefix + "independentSource_mass_split"),
                H("Regroup every full-source mass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Any supported block and its complement reproduce the original mass. The partition is selected after the elementary source law has been defined."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("independent-source-pushforward-regroup"),
                DeclarationHandle.Create(Prefix + "independentSource_pushforward_regroup"),
                H("Preserve every finite readout law"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Reindexing the full finite sum along the standard source partition equivalence leaves every response mass unchanged."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("independent-source-split-law"),
                DeclarationHandle.Create(Prefix + "independentSource_split_law"),
                H("Derive actual block independence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The distribution of the two coordinate blocks equals the product of their induced laws. Empty supported and complementary blocks are included."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("independent-source-pushforward-restrict"),
                DeclarationHandle.Create(Prefix + "independentSource_pushforward_restrict"),
                H("Eliminate unused sources exactly"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a readout that descends through source restriction, the complementary normalized law integrates to one. The remaining pushforward uses only the retained elementary laws."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("independent-source-restriction-marginal"),
                DeclarationHandle.Create(Prefix + "independentSource_restriction_marginal"),
                H("Recover the actual restriction marginal"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Coordinate restriction pushes the full source law to the elementary product law on precisely the retained coordinates."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("independent-source-readout-law-invariant"),
                DeclarationHandle.Create(Prefix + "independentSource_readout_law_invariant"),
                H("Insensitivity to unused disturbance laws"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a fixed supported readout, two elementary law families that agree on the support have identical output distributions. Structural equations and readouts remain fixed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("joint-event-constraint-projection-iff"),
                DeclarationHandle.Create(Prefix + "joint_event_constraint_projection_iff"),
                H("Retain constraints while eliminating nuisance parameters"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameter region with observed joint-event probability c and target marginal x projects exactly to c <= x <= 1. When c is positive, dropping the joint-event constraint would incorrectly allow x = 0."))),
                DescribeRole.Theorem))));
}
