using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.AlgebraicBoundary;

internal sealed class Source_TauCeti_Data_Nat_Choose_BasicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pinned real algebraic source: TauCeti.Data.Nat.Choose.Basic.",
        H("Pinned real algebraic source: TauCeti.Data.Nat.Choose.Basic."),
        Blocks(Paragraph(Text("This content adaptation retains selected declarations and their proof bodies from TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2, TauCeti/Data/Nat/Choose/Basic.lean. The retained declarations give the second binomial coefficient of a sum and the falling-factorial weighted Vandermonde identity. The D5 import paths connect its actual proof dependencies to the original cone boundary consumer. It does not assume a cylindrical decomposition or semialgebraic projection certificate. The original source ownership is retained and no independent escape credit is claimed. Full license and attribution appear in the Lean source and docs/reports/licenses/TauCeti-LICENSE.txt. Each adaptation is retired when the actual pinned mathlib supplies an equivalent statement, replacing consumers by direct applications of that owner.")),
        Paragraph(Text("For all natural A,i,m, multiplying choose(A,i) by the descending factorial i↓m lowers both binomial indices and contributes A↓m, with the original out-of-range convention giving zero. Pinned factorial/choose identities prove this, including i<m and m>A. Summing against choose(B,r-i) and applying pinned Vandermonde after the index shift gives A↓m times choose(A+B-m,r-m), under exactly the original bounds. The unweighted and zero-order cases are included. The surviving add_choose_two supplies the signed degree-drop exponent identity.")))));
}
