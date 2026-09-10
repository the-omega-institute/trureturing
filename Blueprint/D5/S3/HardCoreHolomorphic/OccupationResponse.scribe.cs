using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HardCoreHolomorphic;

internal sealed class OccupationResponseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual occupation, normalized Gibbs probabilities and analytic response.",
        H("OccupationResponse"),
        Blocks(
            Describe.Lean(DescribeId.Create("hc-occupation-occupationresponse-grid-partition-occupation-identity"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/OccupationResponse.grid_partition_occupation_identity"),
                H("grid partition occupation identity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact entire-plane occupation identity for the original square-grid sum. No nonvanishing or probability interpretation is needed for this equation."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-occupation-occupationresponse-normalized-log-first-moment"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/OccupationResponse.normalized_log_first_moment"),
                H("normalized log first moment"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The normalized logarithm's scaled derivative is the actual first moment normalized by the actual partition. The z=0 endpoint is included."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-occupation-occupationresponse-normalized-log-occupation-identity"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/OccupationResponse.normalized_log_occupation_identity"),
                H("normalized log occupation identity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual analytic response equals the sum of actual one-vertex occupied ratios. General complex values are analytic quantities, not probabilities."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-occupation-occupationresponse-normalized-log-scaled-response-bound"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/OccupationResponse.normalized_log_scaled_response_bound"),
                H("normalized log scaled response bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A graph-size-linear bound on the complex scaled response, using the previous actual marked-vacancy bound and preserving the same common tube."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-occupation-occupationresponse-real-gibbs-log-derivative"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/OccupationResponse.real_gibbs_log_derivative"),
                H("real Gibbs log derivative"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The real Gibbs mean is exactly the scaled derivative of the already-owned normalized complex log at the same real activity. No derivative transport or unspecified probabilistic model is assumed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-occupation-occupationresponse-gibbs-expected-card-is-log-response"),
                DeclarationHandle.Create("D5/S3/HardCoreHolomorphic/OccupationResponse.gibbs_expected_card_is_log_response"),
                H("Gibbs expected card is log response"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A direct finite-PMF expectation statement at the analytic endpoint. This binds the claimed physical observable to the actual sampled configurations."))), DescribeRole.Theorem))));
}
