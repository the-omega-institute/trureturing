using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class FiniteApproximationCodeBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite set of codes in the first N approximation stages. Its complement has stage at least N, uniformly in the represented finite quotient point. This is the finite-support estimate needed to prove that the actual free representative differences have diagonal infinity fibers. It includes empty and finite S. New proofs, Apache-2.0; Rodriguez Camargo, Notes on Solid Geometry, Lemma 3.3.2.",
        H("Finite Approximation Code Bounds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-finiteapproximationcodebounds-finiteapproximationstagecodes-mem"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/FiniteApproximationCodeBounds.finiteApproximationStageCodes_mem"),
                H("finite Approximation Stage Codes mem"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. The finite set of codes in the first N approximation stages. Its complement has stage at least N, uniformly in the represented finite quotient point. This is the finite-support estimate needed to prove that the actual free representative differences have diagonal infinity fibers. It includes empty and finite S. New proofs, Apache-2.0; Rodriguez Camargo, Notes on Solid Geometry, Lemma 3.3.2."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-finiteapproximationcodebounds-finiteapproximationindex-stage-eventually"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/FiniteApproximationCodeBounds.finiteApproximationIndex_stage_eventually"),
                H("finite Approximation Index stage eventually"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. The finite set of codes in the first N approximation stages. Its complement has stage at least N, uniformly in the represented finite quotient point. This is the finite-support estimate needed to prove that the actual free representative differences have diagonal infinity fibers. It includes empty and finite S. New proofs, Apache-2.0; Rodriguez Camargo, Notes on Solid Geometry, Lemma 3.3.2."))),
                DescribeRole.Theorem))));
}
