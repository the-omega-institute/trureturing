using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.LinearForests;

internal sealed class AlternatingForestSuccessorBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Remaining heads control a connector in an alternating cycle completion.",
        H("Successors of a component in an oriented alternating forest"),
        Blocks(Describe.Lean(
            DescribeId.Create("oriented-weld-successor-component-bound"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/Graph/LinearForests/AlternatingForestSuccessorBound.mass_of_successor_components"),
            H("Probability bound for a set of successor components"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Prescribe directed edges on a finite set with n vertices of each color. "
                + "Let m be the number of prescribed edges "
                + "and assume m plus two is at most n. Sample a uniform directed alternating single cycle "
                + "that extends all prescribed edges. The sampled cycle forces the prescribed "
                + "edges to alternate and to have at most one incoming and outgoing edge per "
                + "vertex. Any directed loop among them would traverse the whole cycle, "
                + "contradicting the strict edge bound. Each path component has a head and a tail. "
                + "Given a component and a set of other components, the probability that the "
                + "successor of its tail is a head in that set is at most the size of the set "
                + "divided by n minus m minus one. Each prescribed edge can remove at most one "
                + "head of either color, so the remaining count supplies the denominator."))),
            DescribeRole.Theorem))));
}
