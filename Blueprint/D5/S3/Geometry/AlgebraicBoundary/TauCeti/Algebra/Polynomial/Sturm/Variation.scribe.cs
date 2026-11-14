using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.AlgebraicBoundary;

internal sealed class Source_TauCeti_Algebra_Polynomial_Sturm_VariationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pinned real algebraic source: TauCeti.Algebra.Polynomial.Sturm.Variation.",
        H("Pinned real algebraic source: TauCeti.Algebra.Polynomial.Sturm.Variation."),
        Blocks(Paragraph(Text("This content adaptation retains selected declarations and proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/Algebra/Polynomial/Sturm/Variation.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.")),
        Paragraph(Text("The signs along the retained Sturm sequence obey its actual remainder recurrence. Simultaneous evaluation zeros propagate along the recurrence; at an isolated zero the neighboring nonzero entries have opposite signs, and deleting the zero leaves the appropriate variation unchanged. The initial-zero branch contributes the stated one-step correction. Common scaling and simultaneous negation use pinned sign multiplication and the list variation equations, with explicit zero/nonzero branches. These readouts are applications of the recurrence at the original point, not extra assumptions of Sturm regularity.")))));
}
