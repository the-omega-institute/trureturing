using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.AlgebraicBoundary;

internal sealed class Source_TauCeti_Algebra_Polynomial_RolleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pinned real algebraic source: TauCeti.Algebra.Polynomial.Rolle.",
        H("Pinned real algebraic source: TauCeti.Algebra.Polynomial.Rolle."),
        Blocks(Paragraph(Text("This content adaptation retains selected declarations and proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/Algebra/Polynomial/Rolle.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.")),
        Paragraph(Text("PolynomialRolle R is the quantified implication that between two distinct zeros of a polynomial there is a zero of its derivative. Supplying a proof for every p,a,b with the original endpoint and order premises is exactly supplying this proposition; the identity constructor introduces those variables directly. The real-closed-field derivation remains the actual source of the Rolle conclusion, including the constant-zero case.")))));
}
