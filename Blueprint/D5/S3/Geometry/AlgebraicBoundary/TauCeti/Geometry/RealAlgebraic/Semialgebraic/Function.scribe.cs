using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.AlgebraicBoundary;

internal sealed class Source_TauCeti_Geometry_RealAlgebraic_Semialgebraic_FunctionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pinned real algebraic source: TauCeti.Geometry.RealAlgebraic.Semialgebraic.Function.",
        H("Pinned real algebraic source: TauCeti.Geometry.RealAlgebraic.Semialgebraic.Function."),
        Blocks(Paragraph(Text("This content adaptation retains selected declarations and proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/Geometry/RealAlgebraic/Semialgebraic/Function.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.")),
        Paragraph(Text("IsSemialgebraicMap is semialgebraicity of the graph, and IsSemialgebraicOn restricts that graph to the original domain. Equality on that domain gives the same graph. Constants, identity and polynomial evaluation are finite coordinate polynomial equations; the empty restriction has empty graph. Gluing on the stated semialgebraic pieces takes the union of their restricted graphs, with the original agreement conditions ensuring the result is a function. The original finite-coordinate, coefficient and projection hypotheses are retained for every operation; graph rewriting alone supplies these special applications.")))));
}
