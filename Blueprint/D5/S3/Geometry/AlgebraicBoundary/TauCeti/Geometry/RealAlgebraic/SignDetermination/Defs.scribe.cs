using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.AlgebraicBoundary;

internal sealed class Source_TauCeti_Geometry_RealAlgebraic_SignDetermination_DefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pinned real algebraic source: TauCeti.Geometry.RealAlgebraic.SignDetermination.Defs.",
        H("Pinned real algebraic source: TauCeti.Geometry.RealAlgebraic.SignDetermination.Defs."),
        Blocks(Paragraph(Text("This content adaptation retains selected declarations and proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/Geometry/RealAlgebraic/SignDetermination/Defs.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.")),
        Paragraph(Text("For a finite set Z and a polynomial p over a linearly ordered semiring, signSum Z p is the integer sum of sign(p(x)) over x:Z. Finset.sum_coe_sort is its direct sum over Z. Over a linearly ordered integral domain, tarskiQuery p q is signSum p.roots.toFinset q, so p=0 gives zero under the polynomial roots convention. Counting the three sign fibers gives positive count minus negative count, with zero signs contributing nothing. This counting identity is the pinned fiberwise-sum application; the useful root-locus argument uses the actual Cauchy-index/signed-PSC identity and its arbitrary Euclidean-depth induction.")))));
}
