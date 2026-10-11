using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class MeasureTailsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual protected-P tail map needed for the two-sided bounded-measure inverse: F_P(e_n tensor e_j) = e_j if n <= j, and zero otherwise. The pointed map is continuous and vanishes on both infinity fibers, so it descends through both exact protected cokernels. Its zeroth-row section is proved, rather than assumed. New proofs, Apache-2.0; the construction is in Rodriguez Camargo's Notes on Solid Geometry, Lemma 3.3.3, and the checked immutable realization response supplied by root.",
        H("Measure Tails"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-measuretails-measureptailzeronumerator-relation"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/MeasureTails.measurePTailZeroNumerator_relation"),
                H("measure PTail Zero Numerator relation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. The actual protected-P tail map needed for the two-sided bounded-measure inverse: F_P(e_n tensor e_j) = e_j if n <= j, and zero otherwise. The pointed map is continuous and vanishes on both infinity fibers, so it descends through both exact protected cokernels. Its zeroth-row section is proved, rather than assumed. New proofs, Apache-2.0; the construction is in Rodriguez Camargo's Notes on Solid Geometry, Lemma 3.3.3, and the checked immutable realization response supplied by root."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-measuretails-measureptailsection-tail"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/MeasureTails.measurePTailSection_tail"),
                H("measure PTail Section tail"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("F_P epsilon_P = 1, the second inverse identity required by the bounded measure argument. This is an actual equality of condensed morphisms."))),
                DescribeRole.Theorem))));
}
