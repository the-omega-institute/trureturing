using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Probability;

internal sealed class NamingUpdateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite random injective naming can be conditioned on additional assigned names.",
        H("Updating a partially observed naming"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unused"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Probability/NamingUpdate.unused"),
                H("The remaining available names"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Remove the values of the expanded naming from the original available set."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("agrees"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Probability/NamingUpdate.agrees"),
                H("Agreement with an expanded assignment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A full injective naming agrees with the assigned value at each vertex " +
                    "of the expanded assignment."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("uniform-after-reveal"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Probability/NamingUpdate.uniform_after_reveal"),
                H("The remaining completions have a uniform conditional law"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix finite vertex and name sets. An initial injective assignment " +
                        "names some vertices, and the other vertices use the available names. " +
                        "Take an expanded injective assignment on a superset of the initially " +
                        "named vertices. It extends the fixed names and uses available names " +
                        "on the newly assigned vertices. Assume an original completion agrees " +
                        "with the expanded assignment.")),
                    Paragraph(Text(
                        "The agreeing original completions correspond bijectively to the " +
                        "completions of the expanded assignment using the remaining names. " +
                        "The correspondence preserves the full naming. Filtering the uniform " +
                        "original law on agreement and forgetting the completion condition gives " +
                        "the same distribution as forgetting the condition on the uniform new law.")),
                    Paragraph(Text(
                        "Every agreeing injection avoids the newly fixed values away from " +
                        "the expanded domain. Conversely a new completion satisfies the " +
                        "original assignment and availability requirements. The two uniform " +
                        "laws agree after transport by this bijection."))),
                DescribeRole.Theorem))));
}
