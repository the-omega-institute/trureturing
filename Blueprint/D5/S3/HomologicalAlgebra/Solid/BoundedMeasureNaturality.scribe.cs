using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class BoundedMeasureNaturalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Naturality of the actual bounded-family lift and independence of its finite coefficient range. New proofs, Apache-2.0. The free-tensor naturality proof is the right-variable companion to the attributed freeTensorIsoInt proof in DiscreteInt, using the official Mathlib monoidal APIs.",
        H("Bounded Measure Naturality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-boundedmeasurenaturality-boundedcoefficientmap-range-independent"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/BoundedMeasureNaturality.boundedCoefficientMap_range_independent"),
                H("bounded Coefficient Map range independent"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. Naturality of the actual bounded-family lift and independence of its finite coefficient range. New proofs, Apache-2.0. The free-tensor naturality proof is the right-variable companion to the attributed freeTensorIsoInt proof in DiscreteInt, using the official Mathlib monoidal APIs."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-boundedmeasurenaturality-boundedfamilylocallift-range-independent"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/BoundedMeasureNaturality.boundedFamilyLocalLift_range_independent"),
                H("bounded Family Local Lift range independent"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. Naturality of the actual bounded-family lift and independence of its finite coefficient range. New proofs, Apache-2.0. The free-tensor naturality proof is the right-variable companion to the attributed freeTensorIsoInt proof in DiscreteInt, using the official Mathlib monoidal APIs."))),
                DescribeRole.Theorem))));
}
