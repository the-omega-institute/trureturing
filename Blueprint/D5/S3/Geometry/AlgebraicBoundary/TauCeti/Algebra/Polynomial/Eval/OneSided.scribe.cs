using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.AlgebraicBoundary;

internal sealed class Source_TauCeti_Algebra_Polynomial_Eval_OneSidedDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pinned real algebraic source: TauCeti.Algebra.Polynomial.Eval.OneSided.",
        H("Pinned real algebraic source: TauCeti.Algebra.Polynomial.Eval.OneSided."),
        Blocks(Paragraph(Text("This content adaptation retains selected declarations and proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/Algebra/Polynomial/Eval/OneSided.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.")),
        Paragraph(Text("Over the original linearly ordered coefficient structures, signRight and signLeft are the eventual signs immediately to the right and left of a point. A constant has its coefficient sign. At a root, the sign is the sign of the first nonzero Taylor coefficient, multiplied on the left by (-1) to the root multiplicity. Thus even multiplicity preserves the right sign and odd multiplicity reverses it. Map transport uses the original order-compatible homomorphism, and product, negation and powers use multiplication of signs. These identities follow from the retained root-multiplicity factorization and pinned sign multiplication and eventual-neighborhood laws; the zero polynomial uses sign zero. The actual Sturm interval argument retains the eventual sign witnesses, including roots and zero inputs.")))));
}
