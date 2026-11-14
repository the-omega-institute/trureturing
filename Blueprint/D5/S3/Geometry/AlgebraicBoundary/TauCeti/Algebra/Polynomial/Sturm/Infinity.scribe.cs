using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.AlgebraicBoundary;

internal sealed class Source_TauCeti_Algebra_Polynomial_Sturm_InfinityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pinned real algebraic source: TauCeti.Algebra.Polynomial.Sturm.Infinity.",
        H("Pinned real algebraic source: TauCeti.Algebra.Polynomial.Sturm.Infinity."),
        Blocks(Paragraph(Text("This content adaptation retains selected declarations and their original proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/Algebra/Polynomial/Sturm/Infinity.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.")),
        Paragraph(Text("For a finite polynomial sequence over the original ordered field, every polynomial has its eventual leading-term sign at positive and negative infinity. Intersect the finitely many eventual statements to obtain a single bound at which the entire sign list agrees; its sign variation is then constant. The singleton variation is zero by the list definition. These statements use the original nonzero/sign conventions, including zero entries, and are direct finite-filter applications of the retained polynomial asymptotic signs.")))));
}
