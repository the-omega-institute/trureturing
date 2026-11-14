using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.AlgebraicBoundary;

internal sealed class Source_TauCeti_Data_Sym_DisjointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pinned real algebraic source: TauCeti.Data.Sym.Disjoint.",
        H("Pinned real algebraic source: TauCeti.Data.Sym.Disjoint."),
        Blocks(Paragraph(Text("This content adaptation retains selected declarations and proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/Data/Sym/Disjoint.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.")),
        Paragraph(Text("For a family of pairwise disjoint subsets, a multiset containing one point from each indexed subset determines that tuple uniquely: an equal multiset matches each entry with another entry, and disjointness forces the indices equal. The image description is exactly the existence of such a tuple with each coordinate in its assigned subset. The argument uses the original finite index type and disjointness hypotheses, without choosing an ordering of the quotient.")))));
}
