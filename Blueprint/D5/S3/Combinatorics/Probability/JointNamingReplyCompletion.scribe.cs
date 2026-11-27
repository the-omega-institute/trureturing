using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Probability;

internal sealed class JointNamingReplyCompletionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sampling an ordered reply and then completing the naming preserves the joint law.",
        H("Joint law of a reply and its naming completion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("named-after"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Probability/JointNamingReplyCompletion.namedAfter"),
                H("Vertices named after the request"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Take the union of the vertices with fixed names and the range of the request."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("joint-ordered-reply-completion"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Probability/JointNamingReplyCompletion.joint_ordered_reply_completion"),
                H("Read the reply before completing the naming"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix an injective partial naming of a finite vertex set with names from a finite " +
                        "name set. Choose an available subset disjoint from the fixed names and assume " +
                        "there is a completion that uses those names on the remaining vertices. Fix " +
                        "a request with one vertex at each position. The complete-naming experiment " +
                        "samples a completion uniformly and then reads the requested names.")),
                    Paragraph(Text(
                        "The marginal law puts zero mass on inconsistent replies. Each consistent reply " +
                        "has mass equal to the reciprocal of the number of injections from the distinct " +
                        "fresh requested vertices into the available names.")),
                    Paragraph(Text(
                        "For each reply of positive mass there is an expanded partial injective naming " +
                        "that returns the prescribed name at every request position. The completion " +
                        "kernel at that reply samples uniformly from its compatible full namings, using " +
                        "the remaining available names outside the expanded domain. Drawing a reply " +
                        "and then using this kernel has the same joint law of the reply and the full " +
                        "naming as the complete-naming experiment.")),
                    Paragraph(Text(
                        "The observed reply fixes the restriction to the union of old and requested vertices. " +
                        "Name agreement on this union is precisely the observation fiber. Disintegrating " +
                        "the original law over these fibers preserves the paired outcome, and the uniform " +
                        "conditional completion law identifies the concrete kernel."))),
                DescribeRole.Theorem))));
}
