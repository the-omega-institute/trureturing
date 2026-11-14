using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.AlgebraicBoundary;

internal sealed class Source_TauCeti_Geometry_RealAlgebraic_Projection_CollinsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pinned real algebraic source: TauCeti.Geometry.RealAlgebraic.Projection.Collins.",
        H("Pinned real algebraic source: TauCeti.Geometry.RealAlgebraic.Projection.Collins."),
        Blocks(Paragraph(Text("This content adaptation retains selected declarations and proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/Geometry/RealAlgebraic/Projection/Collins.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.")),
        Paragraph(Text("Collins projection is the finite union of the original coefficient, reductum and principal-subresultant families. Its value at the empty family is empty and it is monotone under inclusion by finite union/image membership. Under a coefficient specialization, choose the actual cutoff one above the mapped degree; reductum_map identifies its image and the mapped-degree lemma supplies its degree. Thus the relevant PSC of the two specialized reducta, and the derivative variant, belongs to the image of the same projection family under precisely the original coefficient-ring and HasUniqueDiv hypotheses. No degree-preservation or non-nullification premise is added. The surviving delineability construction uses these actual cutoff witnesses.")))));
}
