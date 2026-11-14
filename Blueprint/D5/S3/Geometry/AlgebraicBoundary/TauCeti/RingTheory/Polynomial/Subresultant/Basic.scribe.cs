using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.AlgebraicBoundary;

internal sealed class Source_TauCeti_RingTheory_Polynomial_Subresultant_BasicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pinned real algebraic source: TauCeti.RingTheory.Polynomial.Subresultant.Basic.",
        H("Pinned real algebraic source: TauCeti.RingTheory.Polynomial.Subresultant.Basic."),
        Blocks(Paragraph(Text("This content adaptation retains selected declarations and proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/RingTheory/Polynomial/Subresultant/Basic.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.")),
        Paragraph(Text("The subresultant matrix entries are the shifted coefficients in the two input blocks, with the original Fin index casts. The zero-index principal subresultant is the fixed-bound resultant determinant; the smaller-bound terminal is the corresponding power of the opposite leading coefficient. Zero matrix/zero-input claims follow entrywise from coefficients of zero and the empty-determinant convention. They use arbitrary commutative coefficients and do not silently assert actual degree equals the formal bounds.")))));
}
