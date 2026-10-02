using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Resource;

internal sealed class SimplexCoverageProbabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual uniform iid physical full-recovery probabilities equal factorial times "
        + "the existing represented spanning polynomial at uniform physical weights.",
        H("Actual Physical Sampling Probability Bridge"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("simplex-coverage-probability-uniform-top"),
                DeclarationHandle.Create(
                    "D5/S3/Resource/SimplexCoverageProbability.uniformSamples_recovered_top"),
                H("All-Horizon Full-Space Recovery Probability"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural t, the existing MinimumRetrievalTime.uniformSamples "
                        + "measure of the existing recovered columns top t event equals "
                        + "ENNReal.ofReal of t! times spanningPolynomial columns bot t evaluated "
                        + "at the constant real coordinate 1/card Index.")),
                    Paragraph(Text(
                        "Disjoint measurable finite prefix-word cylinders partition exactly "
                        + "the actual top-recovery event. The infinite product cylinder formula "
                        + "gives each word probability (1/card Index)^t. Evaluating the "
                        + "spanning-filtered word polynomial gives the same finite sum, and "
                        + "the rational factorial identity identifies it with the original "
                        + "reciprocal-factorial spanning polynomial.")),
                    Paragraph(Text(
                        "The field and ambient module are arbitrary, with no finite-dimensional "
                        + "or spanning premise. All physical indices, including zero, repeated "
                        + "and scalar-parallel columns, remain in the original iid alphabet. "
                        + "The alphabet must be nonempty for the specified uniform measure, "
                        + "and has measurable singletons. Degree zero, zero ambient space and "
                        + "unspanned families are included. No projective pushforward or "
                        + "alternative expected-time definition is introduced."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "Projective transport, orbit averaging, zero-column replacement and the "
                + "all-horizon probability comparison remain separate obligations. The "
                + "existing retrieval_time_probability_bridge supplies the original tail "
                + "and expectation transfer after the required comparison and spanning "
                + "hypotheses are established. The named optimizer remains open."))),
        []));
}
