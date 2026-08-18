using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.EndpointCycle;

internal sealed class GapEndpointsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var large = Id("largeEndpoint");
        var combined = Id("combinedEndpoint");
        var small = Id("smallEndpoint");

        Formula Step(Formula from, Formula to) =>
            Equal(Call("tribonacciPeriodicTransition", from), to);

        var statement = new Formula.Logic(
            new Formula.Logic(Step(large, combined), FormulaLogicOperator.And,
                Step(combined, small)),
            FormulaLogicOperator.And,
            Step(small, large));

        const string declarationPrefix = "D5/S0/Tower/EndpointCycle/GapEndpoints.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "The three gap right endpoints form a transition cycle of period three, each "
                + "coordinate being exactly its own gap's length.",
            H("Gap Endpoints"),
            Blocks(
                Paragraph(Text(
                    "The cycle was found while reconciling two enumeration counts that "
                        + "disagreed. The combinatorial closed-itinerary count and a "
                        + "real-coordinate filter differed by exactly three at period nine, and "
                        + "the three words were the rotations of this cycle. The middle step is "
                        + "where the Tribonacci relation enters: the image coordinate is the "
                        + "square of the constant less the constant less one, which is the "
                        + "constant's inverse, which is the small gap's length.")),
                Describe.Lean(
                    DescribeId.Create("the-gap-endpoints-form-a-three-cycle"),
                    DeclarationHandle.Create(
                        declarationPrefix + "gap_endpoints_form_a_three_cycle"),
                    H("The gap endpoints form a three-cycle"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "A state on this cycle sits on the boundary of its gap, so whether it "
                            + "belongs is a matter of taking gaps closed or half open, not a "
                            + "matter of computing more precisely. Since the cycle has period "
                            + "three it recurs exactly at periods divisible by three, which is "
                            + "where the counts were observed to be unstable."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicEnumeration")),
            ]));
    }
}
