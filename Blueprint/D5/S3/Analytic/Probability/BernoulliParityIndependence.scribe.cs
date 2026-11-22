using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Probability;

internal sealed class BernoulliParityIndependenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independence of parity tests under a finite Bernoulli product law.",
        H("Independence of two Bernoulli parity events"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("parity-events-independent"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Probability/BernoulliParityIndependence.parity_events_independent_iff"),
                H("Disjoint supports and fair bits"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each bit has probability in the half-open interval from zero to one half, " +
                    "with zero excluded and one half included. For each of two subsets, fix the " +
                    "required parity of its bits. The joint event mass equals the product of the " +
                    "individual event masses exactly when the supports are disjoint or a fair " +
                    "bit belongs to their symmetric difference. Multiplying the parity characters " +
                    "cancels the shared signs. In the covariance, the remaining bias product over " +
                    "the symmetric difference multiplies one minus the squared bias product over " +
                    "the intersection. A fair bit can make the first factor vanish. The second " +
                    "factor vanishes exactly when the intersection is empty."))),
                DescribeRole.Theorem))));
}
