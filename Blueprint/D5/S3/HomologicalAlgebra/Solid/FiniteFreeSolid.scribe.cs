using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class FiniteFreeSolidDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual solidity of the free object on a finite light-profinite space, including the empty case. The point/free/discrete comparison is reused from the immutable, independently audited Apache-2.0 CWComparison supplier. This supplies the finite initial term in the concrete generator retract; it makes no bounded-only replacement of the full target. New proofs, Apache-2.0; finite coproduct/limits APIs are from pinned Mathlib.",
        H("Finite Free Solid"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-finitefreesolid-issolid-free-finite"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/FiniteFreeSolid.isSolid_free_finite"),
                H("is Solid free finite"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Solidity follows from a genuine preserved finite coproduct, also for an empty index. No comparison only on ordinary points is substituted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-finitefreesolid-issolid-free-initialcomponent"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/FiniteFreeSolid.isSolid_free_initialComponent"),
                H("is Solid free initial Component"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In particular the actual initial finite quotient used in the retract has a solid free object; it is not silently treated as an infinite space."))),
                DescribeRole.Theorem))));
}
