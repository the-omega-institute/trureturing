using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.AlgebraicBoundary;

internal sealed class Source_TauCeti_Algebra_Polynomial_Sturm_OneSidedDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pinned real algebraic source: TauCeti.Algebra.Polynomial.Sturm.OneSided.",
        H("Pinned real algebraic source: TauCeti.Algebra.Polynomial.Sturm.OneSided."),
        Blocks(Paragraph(Text("This content adaptation retains selected declarations and their original proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/Algebra/Polynomial/Sturm/OneSided.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.")),
        Paragraph(Text("At any point, each polynomial in a finite sequence has the retained eventual sign on the appropriate punctured one-sided neighborhood. Finite intersection gives simultaneous equality of the sign list, so the variation at nearby points equals its one-sided readout. A singleton has zero variations even when its evaluation is zero. No common simple-root hypothesis enters this finite-filter argument.")))));
}
