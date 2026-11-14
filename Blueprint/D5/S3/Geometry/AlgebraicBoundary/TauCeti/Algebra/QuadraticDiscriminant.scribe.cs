using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.AlgebraicBoundary;

internal sealed class Source_TauCeti_Algebra_QuadraticDiscriminantDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pinned real algebraic source: TauCeti.Algebra.QuadraticDiscriminant.",
        H("Pinned real algebraic source: TauCeti.Algebra.QuadraticDiscriminant."),
        Blocks(Paragraph(Text("This content adaptation retains selected declarations and proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/Algebra/QuadraticDiscriminant.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.")),
        Paragraph(Text("For a binary form Q(x,y)=ax²+bxy+cy² over the original strictly ordered commutative ring, 4aQ=(2ax+by)²+(4ac-b²)y². With a>0 and discriminant at most zero this proves Q≥0; representing both signs forces positive discriminant by splitting a<0,a=0,a>0. Over integers, on x=x₀+mk with m>0, choose k by pinned rational round so |2ax+by|≤am. If am<|y| and Q is nonnegative for every k, the completed-square identity forces discriminant≤0. Negative a contradicts nonnegativity at large k; a=0 forces the linear slope to vanish. Thus the same conclusion needs no sign premise on a. Choosing x=y=1+dN with sufficiently large N handles every nonunit d and both nondivisibility conditions. The height condition cannot be discarded: x²-x is nonnegative at every integer but has discriminant one. Expanding b²-4ac modulo four gives b mod two; reducing the same square identity modulo a divisor proves the stated nondivisibility tests for 2ax+b. These are arithmetic applications with the exact integer and order domains, not additional geometric hypotheses.")))));
}
