using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.AlgebraicBoundary;

internal sealed class Source_TauCeti_Data_Finsupp_FinDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pinned real algebraic source: TauCeti.Data.Finsupp.Fin.",
        H("Pinned real algebraic source: TauCeti.Data.Finsupp.Fin."),
        Blocks(Paragraph(Text("This content adaptation retains selected declarations and proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/Data/Finsupp/Fin.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.")),
        Paragraph(Text("Under Zero M, a finitely supported function on Fin n is transported through pinned Finsupp.equivFunOnFinite to a tuple. Appending a value is Fin.snoc and deleting the last coordinate is Fin.init. Pinned Fin.snoc/init equations give the initial and last coordinates, the two inverse laws, injectivity in the pair of arguments and the equality test t=snoc s y iff init t=s and t(last)=y. Under AddZeroClass M, addition is coordinatewise and commutes with cons and snoc. With LT M, the lexicographic tests compare the head then tail for cons, or the initial tuple then last value for snoc, by pinned Fin.pi_lex_lt_cons_cons and the definition Lex.lt_iff. These are transports of the original tuples, including n=0.")))));
}
