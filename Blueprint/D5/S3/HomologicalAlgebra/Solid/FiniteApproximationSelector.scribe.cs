using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class FiniteApproximationSelectorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual continuous pointed coefficient selector for the free-profinite generator retract. At finite row n it selects the code of (n, proj_n(s)); the infinity row is infinity. Every finite fiber is a clopen subset of a single finite row. This proves continuity for empty, finite and infinite S, without enumerating S by N or assuming derived realization. New proofs, Apache-2.0. Research construction: Juan Esteban Rodriguez Camargo, Notes on Solid Geometry, Lemma 3.3.2.",
        H("Finite Approximation Selector"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-finiteapproximationselector-finiteapproximationselectorfun-fiber-clopen"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/FiniteApproximationSelector.finiteApproximationSelectorFun_fiber_clopen"),
                H("finite Approximation Selector Fun fiber clopen"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. The actual continuous pointed coefficient selector for the free-profinite generator retract. At finite row n it selects the code of (n, proj_n(s)); the infinity row is infinity. Every finite fiber is a clopen subset of a single finite row. This proves continuity for empty, finite and infinite S, without enumerating S by N or assuming derived realization. New proofs, Apache-2.0. Research construction: Juan Esteban Rodriguez Camargo, Notes on Solid Geometry, Lemma 3.3.2."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-finiteapproximationselector-finiteapproximationselectorfun-continuous"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/FiniteApproximationSelector.finiteApproximationSelectorFun_continuous"),
                H("finite Approximation Selector Fun continuous"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. The actual continuous pointed coefficient selector for the free-profinite generator retract. At finite row n it selects the code of (n, proj_n(s)); the infinity row is infinity. Every finite fiber is a clopen subset of a single finite row. This proves continuity for empty, finite and infinite S, without enumerating S by N or assuming derived realization. New proofs, Apache-2.0. Research construction: Juan Esteban Rodriguez Camargo, Notes on Solid Geometry, Lemma 3.3.2."))),
                DescribeRole.Theorem))));
}
