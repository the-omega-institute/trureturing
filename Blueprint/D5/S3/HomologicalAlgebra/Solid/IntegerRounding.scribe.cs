using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class IntegerRoundingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Concrete integer rounding for a possible direct cancellation of M_Z/B_Z. Truncated division has uniformly bounded additivity and binary-subdivision defects, independent of the integer and the denominator. These defects can therefore be absorbed in B_Z. This file does not yet construct the condensed null-sequence action or assert quotient vanishing. New proofs, Apache-2.0.",
        H("Integer Rounding"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-integerrounding-integerrounding-dyadic-eventually-zero"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/IntegerRounding.integerRounding_dyadic_eventually_zero"),
                H("integer Rounding dyadic eventually zero"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. Concrete integer rounding for a possible direct cancellation of M_Z/B_Z. Truncated division has uniformly bounded additivity and binary-subdivision defects, independent of the integer and the denominator. These defects can therefore be absorbed in B_Z. This file does not yet construct the condensed null-sequence action or assert quotient vanishing. New proofs, Apache-2.0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-integerrounding-integerrounding-preserves-bound"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/IntegerRounding.integerRounding_preserves_bound"),
                H("integer Rounding preserves bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. Concrete integer rounding for a possible direct cancellation of M_Z/B_Z. Truncated division has uniformly bounded additivity and binary-subdivision defects, independent of the integer and the denominator. These defects can therefore be absorbed in B_Z. This file does not yet construct the condensed null-sequence action or assert quotient vanishing. New proofs, Apache-2.0."))),
                DescribeRole.Theorem))));
}
