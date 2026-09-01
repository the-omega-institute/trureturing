using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Chronology;

internal sealed class ChronologicalSignatureHopfDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Chronology/ChronologicalSignatureHopf.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite step-two chronological signatures satisfy the group-like diagonal and antipode laws, and reverse-and-negate realizes the antipode on event words.",
        H("Chronological Signature Group-Like Hopf Laws"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("coproduct"),
                DeclarationHandle.Create(Prefix + "groupLikeCoproduct"),
                H("Group-like diagonal"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The finite group-like coproduct sends a signature to two identical copies."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("coproduct-mul"),
                DeclarationHandle.Create(Prefix + "group_like_coproduct_mul"),
                H("Multiplicative diagonal"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The diagonal preserves chronological multiplication componentwise."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coassociative"),
                DeclarationHandle.Create(Prefix + "group_like_coproduct_coassociative"),
                H("Coassociative group-like diagonal"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Either order of iterating the diagonal produces three identical signature components."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("left-convolution"),
                DeclarationHandle.Create(Prefix + "antipode_left_convolution"),
                H("Left antipode cancellation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Multiplying the antipode leg by the identity leg yields the empty signature."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("right-convolution"),
                DeclarationHandle.Create(Prefix + "antipode_right_convolution"),
                H("Right antipode cancellation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Multiplying the identity leg by the antipode leg yields the empty signature."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reverse-negate"),
                DeclarationHandle.Create(Prefix + "chronological_signature_reverse_neg"),
                H("Reverse-and-negate realizes the antipode"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Reversing an event word and negating every observed value gives exactly the antipode of its chronological signature."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("log-reverse-negate"),
                DeclarationHandle.Create(Prefix + "chronological_log_reverse_neg"),
                H("Reverse-and-negate in logarithmic coordinates"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "After applying the logarithm, reverse-and-negate becomes coordinatewise negation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reverse-involutive"),
                DeclarationHandle.Create(Prefix + "chronological_signature_reverse_neg_involutive"),
                H("Involutive chronology reversal"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Applying the finite antipode after reverse-and-negate recovers the original signature."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reverse-append"),
                DeclarationHandle.Create(Prefix + "chronological_signature_reverse_neg_append"),
                H("Reversal of concatenation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Reverse-and-negate sends concatenation to the reversed product of the two antipodes."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/Chronology/StepTwoChronologicalLogarithm")),
        ]));
}
