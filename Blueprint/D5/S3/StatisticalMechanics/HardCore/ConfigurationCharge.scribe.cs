using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.HardCore;

internal sealed class ConfigurationChargeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The occupation defect is the expectation of the exact signed configuration charge under one actual common-activity Gibbs law.",
        H("ConfigurationCharge"),
        Blocks(
            Paragraph(Text("The carrier is an arbitrary finite type, including the empty type. The graph is simple and the common real activity lambda is strictly positive. Configurations are all actual independent subsets, including the empty set. The existing GibbsOccupation law gives mass lambda to the power of the configuration cardinality divided by the actual partition sum. Every vertex weight and every expectation below use this same graph and activity.")),
            Describe.Lean(DescribeId.Create("hardcore-charge-occupied-neighbors"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/ConfigurationCharge.occupiedNeighbors"),
                H("Occupied neighbors"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The occupied neighbors of v are precisely the members of J adjacent to v, so their cardinality is the source random variable Y_v."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hardcore-charge-degree-weight"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/ConfigurationCharge.degreeWeight"),
                H("Common-activity degree weight"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The weight q_v is lambda divided by 1 plus (degree(v) plus 1) times lambda; for positive lambda it is also the reciprocal of degree(v) plus 1 plus 1/lambda."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hardcore-charge-configuration-charge"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/ConfigurationCharge.configurationCharge"),
                H("Exact signed configuration charge"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Sum over all v with at least two occupied neighbors of the sum of q_u over those occupied neighbors minus q_v. The charge is signed; neither it nor its expectation is asserted nonnegative."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hardcore-charge-occupation-defect"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/ConfigurationCharge.occupationDefect"),
                H("Actual occupation defect"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The mean actual Gibbs configuration cardinality minus the sum of the degree weights."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hardcore-charge-defect-eq-expectation"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/ConfigurationCharge.defect_eq_expected_charge"),
                H("Actual Gibbs defect equals expected source charge"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("This is the complete source identity: D equals the sum over actual independent configurations J of P(J) times C(J). The finite sum is also written using the existing actual Gibbs PMF. There is no local-balance certificate, assumed normalization, arbitrary marginal law, finite periodic proxy or nonempty-graph premise.")),
                    Paragraph(Text("The proof exchanges the sole occupied neighbor u of v with v. Independence supplies the reverse singleton-neighbor condition; the inverse exchange and equal cardinality preserve the common-activity weight. Opposite directed singleton contributions therefore cancel in expectation. The zero-neighbor contribution follows from the existing actual deletion partition identity and marked-weight identity. Finite double counting and the degree-weight denominator then give the exact defect. Empty carriers and edgeless graphs are included by the same finite sums.")),
                    Paragraph(Text("This is a formalization of the closed configuration-charge identity, not a claim of new literature priority. Its configuration law, deletion partitions, occupation moments and PMF interpretation reuse the existing HardCore declarations. The exchange is a single-configuration construction; no external polynomial product identity is assumed."))),
                DescribeRole.Theorem))));
}
