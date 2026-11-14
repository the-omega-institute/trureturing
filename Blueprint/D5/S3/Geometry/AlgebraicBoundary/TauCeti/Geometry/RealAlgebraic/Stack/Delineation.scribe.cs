using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.AlgebraicBoundary;

internal sealed class Source_TauCeti_Geometry_RealAlgebraic_Stack_DelineationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pinned real algebraic source: TauCeti.Geometry.RealAlgebraic.Stack.Delineation.",
        H("Pinned real algebraic source: TauCeti.Geometry.RealAlgebraic.Stack.Delineation."),
        Blocks(Paragraph(Text("This content adaptation retains selected declarations and proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/Geometry/RealAlgebraic/Stack/Delineation.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.")),
        Paragraph(Text("For the original topological base, family of real polynomials and continuous strictly increasing root functions with supplied degree, multiplicity and exhaustive-root data, Delineation.ofRoots uses precisely those functions and multiplicities. On a preconnected base, sections have constant polynomial sign by continuous-image preconnectedness; each sector has a continuous midpoint or exterior graph meeting every order-connected fiber, so the whole sector is preconnected. The local ball construction restricts these data using Metric.eventually_nhds_iff and convex_ball; it adds no global connectedness premise. Restricting a delineation along a continuous map composes its actual functions and preserves all fields.")),
        Paragraph(Text("The useful general CAD path retains root_notMem_uIcc_of_sign_eval_eq and both implications of mk_mem_sectionSet_iff_of_sign_eval_eq. Positive multiplicity chooses a nonzero polynomial; derivative closure supplies every derivative-sign equality. The live Rolle interval argument then excludes a root between the points. General section and sector semialgebraicity uses shared-root membership and rank loci, including nullified polynomials and empty families.")))));
}
