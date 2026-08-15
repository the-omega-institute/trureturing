using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Diagonal.Extrema;

internal sealed class MaximumDistanceDistributionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var rowCount = Call("rowDistanceCount", F.Id("f"), F.Id("j"));
        var rowPrefix = Call("sum", rowCount, F.Id("j"), D(0), F.Id("r"));
        var boundedListings = Call("maximumDistanceAtMost", F.Id("f"), F.Id("r"));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The maximum diagonal row distance has an exact finite distribution function.",
            H("Maximum Row-Distance Distribution"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("maximum-row-distance-cdf"),
                    DeclarationHandle.Create(
                        "D5/S0/Diagonal/Extrema/MaximumDistanceDistribution.maximum_distance_cdf"),
                    H("Maximum row-distance distribution function"),
                    StatementSource.FromAuthor(Disp(Equal(
                        Call("card", boundedListings),
                        new Formula.Power(rowPrefix, Call("card", F.Id("A")))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The event maximumDistanceAtMost(f,r) consists of the finite listings "
                            + "whose row distance is at most r at every address. The frozen exact "
                            + "distance-profile count identifies each profile fiber with the "
                            + "product of its rowDistanceCount factors. Summing all bounded "
                            + "profiles factors into identical single-row prefix sums, one for "
                            + "each address, and therefore gives the stated card(A)-th power."))),
                    DescribeRole.Theorem))));
    }
}
