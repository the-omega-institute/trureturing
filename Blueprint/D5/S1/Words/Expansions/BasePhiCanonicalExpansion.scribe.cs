using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Expansions;

internal sealed class BasePhiCanonicalExpansionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Natural numbers have a unique finite two-sided canonical base-phi expansion.",
        H("Canonical Two-Sided Base-Phi Expansion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("canonical-two-sided-digits-unique"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Expansions/BasePhiCanonicalExpansion.canonical_two_sided_digits_unique"),
                H("Canonical two-sided digits exist uniquely"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural number N there is exactly one finitely supported "
                    + "integer-indexed digit word with digits at most one, no adjacent ones, "
                    + "and base-phi value equal to N. Uniqueness is proved independently by "
                    + "shifting both finite supports into the nonnegative indices and reading "
                    + "the resulting phi powers as Fibonacci weights. Existence is constructed "
                    + "by a contracting conjugate-window argument."))),
                DescribeRole.Theorem))));
}
