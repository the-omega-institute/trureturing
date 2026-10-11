using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class FiniteApproximationIndexDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual countable indexing and finite stage bounds for the coefficient selector in the free-profinite generator retract. An injection into N is sufficient: no bijection with N is claimed for finite or empty S. New proofs, Apache-2.0. Research construction: Rodriguez Camargo, Notes on Solid Geometry, Lemma 3.3.2.",
        H("Finite Approximation Index"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-finiteapproximationindex-finiteapproximationindexcode-injective"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/FiniteApproximationIndex.finiteApproximationIndexCode_injective"),
                H("finite Approximation Index Code injective"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. Actual countable indexing and finite stage bounds for the coefficient selector in the free-profinite generator retract. An injection into N is sufficient: no bijection with N is claimed for finite or empty S. New proofs, Apache-2.0. Research construction: Rodriguez Camargo, Notes on Solid Geometry, Lemma 3.3.2."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-finiteapproximationindex-finiteapproximationindex-stage-le-bound"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/FiniteApproximationIndex.finiteApproximationIndex_stage_le_bound"),
                H("finite Approximation Index stage le bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. Actual countable indexing and finite stage bounds for the coefficient selector in the free-profinite generator retract. An injection into N is sufficient: no bijection with N is claimed for finite or empty S. New proofs, Apache-2.0. Research construction: Rodriguez Camargo, Notes on Solid Geometry, Lemma 3.3.2."))),
                DescribeRole.Theorem))));
}
