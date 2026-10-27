using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.CubicGain;

internal sealed class MixedTripleExclusionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three complete worlds at a mixed prefix", H("Three complete worlds at a mixed prefix"), Blocks(
            Describe.Lean(DescribeId.Create("mixed-prefix-three-world-exclusion"),
                DeclarationHandle.Create("D5/S3/Observer/CubicGain/MixedTripleExclusion.mixed_prefix_three_world_exclusion"),
                H("Exclusion with both first-response constraints"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix arbitrary real a0, j, m and b, with m-j nonzero, and a chronological word v equal to JM or MJ. The support T consists of exactly three complete worlds with pairwise different sources. Each source is a strictly entrywise positive real two by two matrix of rank one and trace one. Each world has one nonzero entire real gain polynomial of degree at most three and one arbitrary real drift. Every member has initial reading a0, first-J response j, first-M response m, and response b at the actual mixed clock-two matrix. Both first equations constrain the same fixed worlds; they do not denote two acquired reads.")),
                    Paragraph(Text("A response child is the full intersection of the current support with the equality for the next actual read. Every node retains the requirement of at least two complete worlds. The continuation matrices multiply the actual prefix on the left, and the original clocks three through seven are retained. The conclusion excludes five further levels of losing recursion on this support and mixed history.")),
                    Paragraph(Text("For a two-world losing child with at least three remaining levels, every retained continuation is the same whole pair. The equal-trace certificate for three subsequent actions forces equal drifts. The two-action certificate, composed with any fixed earlier continuation, then forces every weighted source difference from its second future clock onward to vanish. Different trace-one sources force both gain samples to be zero.")),
                    Paragraph(Text("In particular, a two-world third child would have gain roots five, six and seven. Its common drift and initial value determine the same entire polynomial at four distinct nodes. A fourth root at clock one or two would violate the nonzero gain condition. The two first-response equalities and the selected mixed second equality then identify the sources, contrary to their distinction. Thus each third action retains all three worlds."))
                ), DescribeRole.Theorem)
        )));
}
