using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class FiniteApproximationTailDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual tail-remainder morphism P tensor free(S) -> free(S). Its finite row n is identity minus r_(n-1), and its infinity row is zero. Row zero is identity minus r_0; the finite initial quotient must therefore be retained in the final retract. No invalid enumeration or free(S)=P assertion is used. New proofs, Apache-2.0; Rodriguez Camargo, Notes on Solid Geometry, Lemma 3.3.2, with the finite initial contribution kept explicit.",
        H("Finite Approximation Tail"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-finiteapproximationtail-finiteapproximationremaindernumerator-relation"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/FiniteApproximationTail.finiteApproximationRemainderNumerator_relation"),
                H("finite Approximation Remainder Numerator relation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. The actual tail-remainder morphism P tensor free(S) -> free(S). Its finite row n is identity minus r_(n-1), and its infinity row is zero. Row zero is identity minus r_0; the finite initial quotient must therefore be retained in the final retract. No invalid enumeration or free(S)=P assertion is used. New proofs, Apache-2.0; Rodriguez Camargo, Notes on Solid Geometry, Lemma 3.3.2, with the finite initial contribution kept explicit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-finiteapproximationtail-finiteapproximationrowsection-remainder"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/FiniteApproximationTail.finiteApproximationRowSection_remainder"),
                H("finite Approximation Row Section remainder"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. The actual tail-remainder morphism P tensor free(S) -> free(S). Its finite row n is identity minus r_(n-1), and its infinity row is zero. Row zero is identity minus r_0; the finite initial quotient must therefore be retained in the final retract. No invalid enumeration or free(S)=P assertion is used. New proofs, Apache-2.0; Rodriguez Camargo, Notes on Solid Geometry, Lemma 3.3.2, with the finite initial contribution kept explicit."))),
                DescribeRole.Theorem))));
}
