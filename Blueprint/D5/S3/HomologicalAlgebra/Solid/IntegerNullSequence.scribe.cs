using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class IntegerNullSequenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual locally constant rounding matrices on the convergent sequence times every light profinite test space. Their additive and binary defects are uniformly bounded, and bounded input remains bounded. These are concrete inputs for direct cancellation of M_Z/B_Z; no condensed action or vanishing is asserted here. New proofs, Apache-2.0.",
        H("Integer Null Sequence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-integernullsequence-integerbinaryroundmatrix-preserves-bound"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/IntegerNullSequence.integerBinaryRoundMatrix_preserves_bound"),
                H("integer Binary Round Matrix preserves bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. Actual locally constant rounding matrices on the convergent sequence times every light profinite test space. Their additive and binary defects are uniformly bounded, and bounded input remains bounded. These are concrete inputs for direct cancellation of M_Z/B_Z; no condensed action or vanishing is asserted here. New proofs, Apache-2.0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-integernullsequence-integerbinaryround-children-defect"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/IntegerNullSequence.integerBinaryRound_children_defect"),
                H("integer Binary Round children defect"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. Actual locally constant rounding matrices on the convergent sequence times every light profinite test space. Their additive and binary defects are uniformly bounded, and bounded input remains bounded. These are concrete inputs for direct cancellation of M_Z/B_Z; no condensed action or vanishing is asserted here. New proofs, Apache-2.0."))),
                DescribeRole.Theorem))));
}
