using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography.MUB;

internal sealed class MUBCompletionConsistencyTransportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Relative-Gram recovery preserves multiplicative transition consistency.",
        H("MUB Completion Consistency Transport"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("consistency-transport-conjugation-product"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBCompletionConsistencyTransport."
                    + "entrywiseConj_mul"),
                H("Entrywise conjugation preserves matrix multiplication"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For complex matrices with a finite shared index type, entrywise "
                    + "conjugation of their product equals the product of their "
                    + "entrywise conjugates in the same order."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("consistency-transport-conjugation-involution"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBCompletionConsistencyTransport."
                    + "entrywiseConj_entrywiseConj"),
                H("Entrywise conjugation is involutive"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Applying entrywise complex conjugation twice returns the original "
                    + "matrix, with no finiteness assumption on its index types."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("consistency-transport-inverse-cardinality"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBCompletionConsistencyTransport."
                    + "entrywiseConj_invCard_smul"),
                H("Conjugation commutes with inverse-cardinality scaling"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any finite type, scaling a complex matrix by the inverse of "
                    + "that type's cardinality commutes with entrywise conjugation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("consistency-transport-recovery-equation"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBCompletionConsistencyTransport."
                    + "recovery_preserves_transition_consistency"),
                H("Recovery preserves transition consistency"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let H, X, Y and P be complex square matrices on a finite coordinate "
                    + "type and let s be a complex scalar. If H times X equals s times "
                    + "the entrywise conjugate of Y, then H times recoverFirst X P equals "
                    + "s times the entrywise conjugate of recoverSecond Y P."))),
                DescribeRole.Theorem))));
}
