using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class MeasureFactorizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual derived factorization of every uniformly bounded integer family through the constructed local reflection of the protected P. The tensor square is proved in BoundedMeasures; no D(Solid) realization is assumed. New proofs, Apache-2.0, following Rodriguez Camargo's concrete measure argument.",
        H("Measure Factorization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-measurefactorization-localptointegermeasures-unit"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/MeasureFactorization.localPToIntegerMeasures_unit"),
                H("local PTo Integer Measures unit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. Actual derived factorization of every uniformly bounded integer family through the constructed local reflection of the protected P. The tensor square is proved in BoundedMeasures; no D(Solid) realization is assumed. New proofs, Apache-2.0, following Rodriguez Camargo's concrete measure argument."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-measurefactorization-boundedfamilylocallift-comparison"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/MeasureFactorization.boundedFamilyLocalLift_comparison"),
                H("bounded Family Local Lift comparison"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every uniformly bounded integer family factors through the actual local reflection of P, with the canonical measure comparison. This is a proved concrete comparison, valid for all light profinite S, not a realization assumption."))),
                DescribeRole.Theorem))));
}
