using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class FiniteApproximationDifferenceRelationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full kernel pair of the actual representative-difference cover is covered by its diagonal and its infinity fiber. Both pieces are closed light-profinite spaces, and their finite coproduct maps surjectively onto the whole relation. These concrete data justify free sheaf descent; equality only on ordinary finite points is not substituted for the kernel-pair relation. New proofs, Apache-2.0; Rodriguez Camargo, Notes on Solid Geometry, Lemma 3.3.2.",
        H("Finite Approximation Difference Relation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-finiteapproximationdifferencerelation-finiteapproximationdifferencerelation-infty-first"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/FiniteApproximationDifferenceRelation.finiteApproximationDifferenceRelation_infty_first"),
                H("finite Approximation Difference Relation infty first"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. The full kernel pair of the actual representative-difference cover is covered by its diagonal and its infinity fiber. Both pieces are closed light-profinite spaces, and their finite coproduct maps surjectively onto the whole relation. These concrete data justify free sheaf descent; equality only on ordinary finite points is not substituted for the kernel-pair relation. New proofs, Apache-2.0; Rodriguez Camargo, Notes on Solid Geometry, Lemma 3.3.2."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-finiteapproximationdifferencerelation-finiteapproximationdifferencerelation-infty-second"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/FiniteApproximationDifferenceRelation.finiteApproximationDifferenceRelation_infty_second"),
                H("finite Approximation Difference Relation infty second"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. The full kernel pair of the actual representative-difference cover is covered by its diagonal and its infinity fiber. Both pieces are closed light-profinite spaces, and their finite coproduct maps surjectively onto the whole relation. These concrete data justify free sheaf descent; equality only on ordinary finite points is not substituted for the kernel-pair relation. New proofs, Apache-2.0; Rodriguez Camargo, Notes on Solid Geometry, Lemma 3.3.2."))),
                DescribeRole.Theorem))));
}
