using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class CoefficientLinearityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Additivity of the concrete bounded coefficient maps, by finite covers of closed coefficient fibers. These maps must be additive before they can be assembled into D : P tensor B_Z -> P. This argument uses actual condensed descent; no injectivity of PToIntegerMeasures is assumed. New proofs, Apache-2.0. The covering epimorphism supplier is reused from root's immutable CWComparison.ProfiniteCover checkpoint, whose copyright and Apache-2.0 attribution are preserved in its frozen source.",
        H("Coefficient Linearity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-coefficientlinearity-measurecoefficientnumerator-prequotient"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/CoefficientLinearity.measureCoefficientNumerator_prequotient"),
                H("measure Coefficient Numerator prequotient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. Additivity of the concrete bounded coefficient maps, by finite covers of closed coefficient fibers. These maps must be additive before they can be assembled into D : P tensor B_Z -> P. This argument uses actual condensed descent; no injectivity of PToIntegerMeasures is assumed. New proofs, Apache-2.0. The covering epimorphism supplier is reused from root's immutable CWComparison.ProfiniteCover checkpoint, whose copyright and Apache-2.0 attribution are preserved in its frozen source."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-coefficientlinearity-boundedcoefficientmap-add"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/CoefficientLinearity.boundedCoefficientMap_add"),
                H("bounded Coefficient Map add"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual coefficient map is additive, before ordinary or derived solidification. This supplies the linearity required for descent to B_Z."))),
                DescribeRole.Theorem))));
}
