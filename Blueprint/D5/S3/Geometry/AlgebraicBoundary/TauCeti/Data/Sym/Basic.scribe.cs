using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.AlgebraicBoundary;

internal sealed class Source_TauCeti_Data_Sym_BasicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pinned real algebraic source: TauCeti.Data.Sym.Basic.",
        H("Pinned real algebraic source: TauCeti.Data.Sym.Basic."),
        Blocks(Paragraph(Text("This content adaptation retains selected declarations and proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/Data/Sym/Basic.lean. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.")),
        Paragraph(Text("The finite symmetric power is the multiset quotient of tuples of fixed length. Mapping and appending commute because they are the corresponding multiset operations, and ofFn of Fin.cons or Fin.append gives singleton addition or append. A tuple is in the image of map exactly when every entry is in the variable map range; choose preimages coordinatewise. The basepoint divisor has n copies of the basepoint, including n=0. Symmetric pairs identify with Sym2 by the two multiset representatives, with the quotient equations proving the inverse laws. All statements retain their original equality/decidability assumptions rather than a hidden order on the carrier.")))));
}
