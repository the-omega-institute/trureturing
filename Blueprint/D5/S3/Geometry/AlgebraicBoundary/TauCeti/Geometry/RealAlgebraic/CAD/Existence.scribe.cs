using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.AlgebraicBoundary;

internal sealed class Source_TauCeti_Geometry_RealAlgebraic_CAD_ExistenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pinned real algebraic source: TauCeti.Geometry.RealAlgebraic.CAD.Existence.",
        H("Pinned real algebraic source: TauCeti.Geometry.RealAlgebraic.CAD.Existence."),
        Blocks(Paragraph(Text("This content adaptation retains selected declarations and their proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/Geometry/RealAlgebraic/CAD/Existence.lean. The retained unconditional producers are exists_isCAD_signInvariant and the HasSemialgebraicProjections instance over the reals. The stronger IsCAD-namespaced sample theorem, including one point per cell, remains in CAD.Basic. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.")))));
}
