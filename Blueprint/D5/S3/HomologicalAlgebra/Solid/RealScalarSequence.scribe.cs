using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class RealScalarSequenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual continuous real scalar null sequence needed by the binary cancellation argument for the bounded-real quotient. This is a function into topological R, not an assertion about modules over discrete R. New proofs, Apache-2.0. The scalar sequence is in Rodriguez Camargo, Notes on Solid Geometry, Proposition 3.2.5.",
        H("Real Scalar Sequence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-realscalarsequence-realbinarydepth-tendsto"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/RealScalarSequence.realBinaryDepth_tendsto"),
                H("real Binary Depth tendsto"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The binary depth tends to infinity; no bounded-index argument is used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-realscalarsequence-realbinaryweight-tendsto"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/RealScalarSequence.realBinaryWeight_tendsto"),
                H("real Binary Weight tendsto"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. The actual continuous real scalar null sequence needed by the binary cancellation argument for the bounded-real quotient. This is a function into topological R, not an assertion about modules over discrete R. New proofs, Apache-2.0. The scalar sequence is in Rodriguez Camargo, Notes on Solid Geometry, Proposition 3.2.5."))),
                DescribeRole.Theorem))));
}
