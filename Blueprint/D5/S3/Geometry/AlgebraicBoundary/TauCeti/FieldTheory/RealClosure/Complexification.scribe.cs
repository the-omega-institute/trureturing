using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.AlgebraicBoundary;

internal sealed class Source_TauCeti_FieldTheory_RealClosure_ComplexificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pinned real algebraic source: TauCeti.FieldTheory.RealClosure.Complexification.",
        H("Pinned real algebraic source: TauCeti.FieldTheory.RealClosure.Complexification."),
        Blocks(Paragraph(Text("This content adaptation retains selected declarations and proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/FieldTheory/RealClosure/Complexification.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.")),
        Paragraph(Text("For the quadratic algebra with i²=-1 over ℝ, send a+bi to Complex.mk a b. The component multiplication equations give the ring/algebra homomorphism and its inverse, so the real and imaginary projections agree exactly. The retained square-root construction has the same nonnegative real part and imaginary sign as Complex.sqrt; its square is the original element. Uniqueness with those branch conditions identifies both roots, including a negative real input and zero. The magnitude is the complex norm, and the real nonnegative square root is Real.sqrt. No choice of the opposite branch is identified with the principal square root.")))));
}
