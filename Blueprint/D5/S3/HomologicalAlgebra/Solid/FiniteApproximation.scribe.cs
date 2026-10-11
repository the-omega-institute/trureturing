using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class FiniteApproximationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compatible finite-image retractions for every light profinite space, using the actual pinned sequential finite presentation. The choices work also for empty and finite spaces; no enumeration of the represented points by N is asserted. These are the finite-approximation data needed for the concrete generator retract in Rodriguez Camargo, Notes on Solid Geometry, Lemma 3.3.2. New proofs, Apache-2.0.",
        H("Finite Approximation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-finiteapproximation-finiteapproximation-range-finite"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/FiniteApproximation.finiteApproximation_range_finite"),
                H("finite Approximation range finite"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. Compatible finite-image retractions for every light profinite space, using the actual pinned sequential finite presentation. The choices work also for empty and finite spaces; no enumeration of the represented points by N is asserted. These are the finite-approximation data needed for the concrete generator retract in Rodriguez Camargo, Notes on Solid Geometry, Lemma 3.3.2. New proofs, Apache-2.0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-finiteapproximation-finiteapproximation-ranges-monotone"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/FiniteApproximation.finiteApproximation_ranges_monotone"),
                H("finite Approximation ranges monotone"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. Compatible finite-image retractions for every light profinite space, using the actual pinned sequential finite presentation. The choices work also for empty and finite spaces; no enumeration of the represented points by N is asserted. These are the finite-approximation data needed for the concrete generator retract in Rodriguez Camargo, Notes on Solid Geometry, Lemma 3.3.2. New proofs, Apache-2.0."))),
                DescribeRole.Theorem))));
}
