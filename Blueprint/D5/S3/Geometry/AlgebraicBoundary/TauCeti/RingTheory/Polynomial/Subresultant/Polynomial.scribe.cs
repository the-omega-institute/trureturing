using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.AlgebraicBoundary;

internal sealed class Source_TauCeti_RingTheory_Polynomial_Subresultant_PolynomialDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pinned real algebraic source: TauCeti.RingTheory.Polynomial.Subresultant.Polynomial.",
        H("Pinned real algebraic source: TauCeti.RingTheory.Polynomial.Subresultant.Polynomial."),
        Blocks(Paragraph(Text("This content adaptation retains selected declarations and proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/RingTheory/Polynomial/Subresultant/Polynomial.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.")),
        Paragraph(Text("Each subresultant coefficient is the determinant of the coefficient matrix with its selected row. RingHom.map_det and coefficient mapping give compatibility under any coefficient homomorphism. Scaling an input scales exactly the number of its columns, and swapping inputs contributes the block sign. The terminal coefficients are triangular diagonal products, including the empty product one; zero input forces a zero column only when that block is nonempty. Polynomial extensionality assembles the coefficient identities, and the stated degree equality is exactly nonvanishing of the top permitted coefficient. No integral-domain or generic-degree assumption is added.")))));
}
