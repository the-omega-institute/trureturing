using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.FourierFibers;

internal sealed class FiniteObservabilityKrylovCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite time-window faithfulness is equivalent to the existing observable Krylov space filling the carrier.",
        H("Finite Observability Krylov Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-hidden-kernel-trivial-iff-observable-krylov-top"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/FourierFibers/FiniteObservabilityKrylovCriterion.finite_hidden_kernel_trivial_iff_observable_krylov_top"),
                H("Trivial hidden kernel equals full Krylov span"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The finite common kernel of all delayed readouts is trivial exactly when the observable Krylov subspace is the whole finite-dimensional carrier.")),
                    Paragraph(Text(
                        "This node reuses Trueturning's frozen orthogonal-duality theorem and Mathlib's orthogonal-complement criterion instead of introducing a parallel observability theory."))),
                DescribeRole.Theorem))));
}
