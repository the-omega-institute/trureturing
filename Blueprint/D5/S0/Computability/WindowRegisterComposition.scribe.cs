using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class WindowRegisterCompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four registers in one visited frame.",
        H("Four registers in one visited frame"),
        Blocks(
            Paragraph(Text("The same finite program applies the single-register phase successively to four fixed targets. Already completed targets are retained; each remaining target is blank when entered. The packed tape and unrelated tracks are unchanged.")),
            Paragraph(Text("The four phases share a single head interval. Their finite transitions and actual costs compose into one run, while storage is bounded by historical positions in that interval. The final tapes contain the four separately normalized packed lanes.")),
            Describe.Lean(DescribeId.Create("all-registers"), DeclarationHandle.Create("D5/S0/Computability/WindowRegisterComposition.all_registers"), H("all registers"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("With all declared parameters and hypotheses, the exact statement is: all_registers (m : Track \u2192 \u2124 \u2192 Symbol) (h : Track \u2192 \u2124) (bs : List Bits) (W : \u2115) (hW : bs.length+2 \u2264 W) (hh : \u2200 t,0\u2264h t \u2227 h t\u2264W) (hw : h workTrack=0) (hj : \u2200 j : Lane,h (target j)=0) (mw : m workTrack=word bs) (mj : \u2200 j : Lane,m (target j)=fun _=>.blank) : \u2203 T : \u2115, T\u2264128*(bs.length+1)+4 \u2227 run (entry m h 0) T=startAt m h bs 4 \u2227 program (startAt m h bs 4).control=.halt \u2227 (\u2200 n\u2264T,Heads W (run (entry m h 0) n)) \u2227 \u2200 j : Lane,(startAt m h bs 4).cell (target j)=register bs j"))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/WindowRegisterTrim"))]));
}
