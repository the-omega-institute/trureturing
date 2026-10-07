using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class FiniteApproximationCoefficientDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual coefficient morphism D_S : P tensor free(S) -> P for the free-profinite generator retract. It descends the continuous representative selector through the exact protected infinity cokernel. This is an ordinary condensed morphism, with no realization or derived-adjunction premise. New proofs, Apache-2.0; Rodriguez Camargo, Notes on Solid Geometry, Lemma 3.3.2.",
        H("Finite Approximation Coefficient"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-finiteapproximationcoefficient-finiteapproximationcoefficientnumerator-relation"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/FiniteApproximationCoefficient.finiteApproximationCoefficientNumerator_relation"),
                H("finite Approximation Coefficient Numerator relation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. The actual coefficient morphism D_S : P tensor free(S) -> P for the free-profinite generator retract. It descends the continuous representative selector through the exact protected infinity cokernel. This is an ordinary condensed morphism, with no realization or derived-adjunction premise. New proofs, Apache-2.0; Rodriguez Camargo, Notes on Solid Geometry, Lemma 3.3.2."))),
                DescribeRole.Theorem))));
}
