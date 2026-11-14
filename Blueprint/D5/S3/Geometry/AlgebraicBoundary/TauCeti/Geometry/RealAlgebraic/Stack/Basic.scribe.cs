using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.AlgebraicBoundary;

internal sealed class Source_TauCeti_Geometry_RealAlgebraic_Stack_BasicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pinned real algebraic source: TauCeti.Geometry.RealAlgebraic.Stack.Basic.",
        H("Pinned real algebraic source: TauCeti.Geometry.RealAlgebraic.Stack.Basic."),
        Blocks(Paragraph(Text("This content adaptation retains selected declarations and proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/Geometry/RealAlgebraic/Stack/Basic.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.")),
        Paragraph(Text("Given θ:Fin k→X→α, sectionSet θ i is the graph {(x,t) | θ i x=t}. For linearly ordered α, sectorSet θ j consists of (x,t) with θ i x<t for i.castSucc<j and t<θ i x for j≤i.castSucc. These are literal membership formulas, and pullback along any f:Y→X substitutes f into θ. For C⊆(Fin n→α), cylinder C (x,t)=Fin.cons t x.val; its zero coordinate is t and its tail is x.val. Its range is exactly {y | Fin.tail y∈C}, with inverse y↦((Fin.tail y,proof),y 0). stackCells is the union of the ranges of the images of all sections and sectors. These definitions include k=0, when the unique sector is the entire cylinder. All general continuity, preconnected-fiber, strict-order and disjointness arguments use these same definitions.")))));
}
