using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class MeasureSelectorsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The concrete bounded-coefficient tensor square for the measure comparison. For every light profinite test space S and every uniformly finite-range family of integer coordinates, construct the map P tensor Z[S] -> P by selecting finite points in the convergent sequence. This works for empty, finite and infinite S. The uniform bound is essential; no bound is imposed on the number of coordinates. New proofs, Apache-2.0, following the construction in Rodriguez Camargo, Notes on Solid Geometry, Lemma 3.3.3.",
        H("Measure Selectors"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-measureselectors-coefficientselectorfun-fiber-clopen"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/MeasureSelectors.coefficientSelectorFun_fiber_clopen"),
                H("coefficient Selector Fun fiber clopen"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. The concrete bounded-coefficient tensor square for the measure comparison. For every light profinite test space S and every uniformly finite-range family of integer coordinates, construct the map P tensor Z[S] -> P by selecting finite points in the convergent sequence. This works for empty, finite and infinite S. The uniform bound is essential; no bound is imposed on the number of coordinates. New proofs, Apache-2.0, following the construction in Rodriguez Camargo, Notes on Solid Geometry, Lemma 3.3.3."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-measureselectors-coefficientselectorfun-continuous"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/MeasureSelectors.coefficientSelectorFun_continuous"),
                H("coefficient Selector Fun continuous"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Continuity at infinity uses only preservation of the finite index: every output is either the input index or infinity. No convergence of c_n is needed."))),
                DescribeRole.Theorem))));
}
