using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.AlgebraicBoundary;

internal sealed class Source_TauCeti_Algebra_MvPolynomial_EquivDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pinned real algebraic source: TauCeti.Algebra.MvPolynomial.Equiv.",
        H("Pinned real algebraic source: TauCeti.Algebra.MvPolynomial.Equiv."),
        Blocks(Paragraph(Text("This content adaptation retains selected declarations and proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/Algebra/MvPolynomial/Equiv.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.")),
        Paragraph(Text("For every commutative ring R and distinguished Fin coordinate p, finSuccEquiv' separates that variable as the univariate X and the remaining variables through succAbove. Its inverse, coefficient, constant and rename identities follow by extensionality on variables and pinned rename/aeval laws. Conjugating Polynomial.derivative by this equivalence gives an R-linear derivation; pinned MvPolynomial.derivation_ext checks its value at each variable and proves the exact pderiv transport. In the last-coordinate convention, composing the outer univariate lcoeff with the inner multivariate lcoeff is an R-linear map. MvPolynomial.linearMap_ext reduces its arbitrary-polynomial equality to monomials; Fin.snoc/init equations identify the exact exponent. The actual Collins and coefficient-matrix coordinate equivalences remain the same Fin maps, with all cast and index inequalities.")))));
}
