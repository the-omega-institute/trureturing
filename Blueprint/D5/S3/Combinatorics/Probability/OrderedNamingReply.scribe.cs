using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Probability;

internal sealed class OrderedNamingReplyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact distribution of ordered answers under a uniform injective naming.",
        H("The law of an ordered naming reply"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fresh-vertices"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Probability/OrderedNamingReply.FreshVertices"),
                H("Distinct requested vertices without fixed names"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Take the vertices in the range of the request that lie outside the set " +
                    "with fixed names. Several request positions can select the same vertex."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("consistent-reply"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Probability/OrderedNamingReply.IsConsistentReply"),
                H("Consistency of a reply"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A consistent reply returns each fixed name at every position selecting its vertex " +
                    "and chooses an available name for each remaining position. Two positions have the " +
                    "same returned name exactly when they select the same vertex."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ordered-reply-mass"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Probability/OrderedNamingReply.ordered_reply_mass"),
                H("Mass of an ordered reply"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix a partial injective naming of a finite vertex set with names from a finite " +
                        "name set. Choose an available set of names disjoint from the fixed names and " +
                        "assume there is at least one injective completion using only available names " +
                        "for vertices without a fixed name. Sample a completion uniformly and return " +
                        "the names at the vertices selected by the fixed request.")),
                    Paragraph(Text(
                        "A consistent reply has mass equal to the reciprocal of the number of injections " +
                        "from the distinct requested vertices without fixed names into the available " +
                        "names. An inconsistent reply has zero mass.")),
                    Paragraph(Text(
                        "Each consistent reply reconstructs a unique injection of the distinct requested " +
                        "vertices without fixed names. Choosing a request position for a vertex recovers " +
                        "its name, and the equality pattern makes the choice immaterial. The uniform law " +
                        "on these injections gives the exact mass through this correspondence."))),
                DescribeRole.Theorem))));
}
