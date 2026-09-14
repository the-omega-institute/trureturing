using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.GoldenTomography;

internal sealed class PositiveMomentPlateauDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A long hidden moment plateau is compatible with two bounded positive spectral measures.",
        H("Positive spectral plateau obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("positive-spectral-moment-plateau"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/GoldenTomography/PositiveMomentPlateau.positive_moment_plateau"),
                H("An arbitrary finite plateau inside bounded positive spectral pairs"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For any finite injective real node family in [0,1] and any positive "
                        + "mass budget, there exist a positive height delta and two nonnegative "
                        + "weight families whose combined mass is at most the budget. Their "
                        + "moment difference equals delta at every index below the number of "
                        + "nodes, and belongs to [0,delta] at every natural index.")),
                    Paragraph(Text(
                        "The witness is an actual finite exponential family. Recursive spectral "
                        + "weights give f(0)=1 and f(n+1)=a*f(n)+(1-a)*v(n), where v is the "
                        + "one-node-shorter witness. Induction proves the all-time bounds and "
                        + "the exact prefix. Splitting the signed weights into their positive "
                        + "and negative parts and normalizing by their finite absolute mass "
                        + "produces the two bounded positive measures. The gap divisions "
                        + "construct a lower-bound example; no uniform separation assumption "
                        + "is proposed for a recovery guarantee. The empty node family is "
                        + "included with a vacuous plateau.")),
                    Paragraph(Text(
                        "The declaration does not assert an explicit exponential bound on "
                        + "the reciprocal height, a block-operator realization, a Markov "
                        + "embedding, or the complete noise-rate theorem. Those are distinct "
                        + "ordinary mathematical arguments in the accompanying theory."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Analytic/GoldenTomography/FinitePronyHankelReconstruction")),
        ]));
}
