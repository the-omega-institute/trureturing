using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.AnalyticClosure.Polylogarithm;

internal sealed class CompositionRecurrencesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/AnalyticClosure/Polylogarithm/CompositionRecurrences.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual strict source series satisfies both differential recurrences, including at zero.",
        H("CompositionRecurrences"), Blocks(
            Describe.Lean(DescribeId.Create("differentiate-source-series"),
                DeclarationHandle.Create(Prefix + "source_derivative"),
                H("Termwise derivative of the strict source sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/AnalyticClosure/xu2026rational")),
                Blocks(Paragraph(Text(
                    "At each point in the unit disk, choose a larger radius still below one. "
                    + "The source-specific coefficient bound gives a summable common majorant "
                    + "for the differentiated terms on that disk. The derivative is the actual "
                    + "series with the head exponent decreased by one; exponent zero is included. "
                    + "The termwise differentiation theorem is applied directly from Mathlib."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("source-recurrences-at-origin"),
                DeclarationHandle.Create(Prefix + "source_recurrences"),
                H("Both recurrences with the correct removable values"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/AnalyticClosure/xu2026rational")),
                Blocks(Paragraph(Text(
                    "For leading one, the derivative equals source(tail)/(1-z) throughout the disk, "
                    + "with source(empty)=1. The strict finite-sum difference telescopes only after "
                    + "summability of the shifted series has been proved. For head greater than one, "
                    + "the derivative equals source(head-1,tail)/z away from zero; at zero it is one "
                    + "for an empty tail and zero otherwise. Total division by zero is never used "
                    + "as that removable value. These identities are premises proved within the "
                    + "source unit, not hypotheses of its all-composition disk consumer."))), DescribeRole.Theorem))));
}
