using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Deficit.Beatty;

internal sealed class GoldenObserverRouteDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden observer exponent has sqrt-five drift and exactly two golden step sizes.",
        H("Golden Observer Beatty Route"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-observer-sqrt-five-drift-and-two-distances"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Beatty/GoldenObserverRoute."
                    + "golden_observer_route_w_c1"),
                H("The golden observer has sqrt-five drift and two golden distances"),
                StatementSource.FromAuthor(WC1Formula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Here phi=(1+sqrt(5))/2, psi=1-phi, "
                        + "beatty(v)=floor((v+1)phi)-1, beta(v)=beatty(v)-v psi, "
                        + "and r is the displayed fractional remainder. These four definitions "
                        + "are transcribed from the frozen Hearts module; the proof module does "
                        + "not import that frontier.")),
                    Paragraph(Text(
                        "Splitting a real number into its integer floor and fractional part gives "
                        + "the drift formula and the left-open, right-closed remainder window. "
                        + "The floor increment lies between one and two because 1<phi<2. "
                        + "Subtracting psi then turns those two integer increments into phi and "
                        + "phi squared, respectively.")),
                    Paragraph(Text(
                        "This is the Appendix III correction of W-C1. The superseded distance "
                        + "pair involving sqrt(5)+phi-2 and sqrt(5)+phi-1 is not asserted. "
                        + "The final equality records the requested beta(2)-beta(1)=phi anchor.")),
                    Paragraph(Text(
                        "Pinned Mathlib and the repository were searched before proving. Mathlib "
                        + "supplies the floor, fractional-part, and golden-ratio component laws, "
                        + "but neither source contains this observer-specific conjunction."))),
                DescribeRole.Theorem))));

    private static Formula WC1Formula()
    {
        Formula v = F.Id("v");
        Formula successor = Seq(v, Plus, D(1));
        Formula betaV = Call("beta", v);
        Formula betaSuccessor = Call("beta", successor);
        Formula remainderV = Call("r", v);
        Formula shiftedPhase = Grp(Grp(v, Plus, D(1)), Times, Varphi);
        Formula gap = Seq(betaSuccessor, Sp, Minus, Sp, betaV);
        Formula beattyIncrement = Seq(
            Call("beatty", successor), Sp, Minus, Sp, Call("beatty", v));
        Formula remainderWindow = Seq(
            Open, Varphi, Sp, Minus, Sp, D(2), Comma, Sp,
            Varphi, Sp, Minus, Sp, D(1), CloseBracket);
        Formula twoDistances = new Formula.SetLiteral([
            Varphi,
            Seq(Varphi, Caret, Grp(D(2)))
        ]);

        return Disp(Seq(
            Open, Forall, Sp, v, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma,
            RowBreak,
            betaV, Sp, Eq, Sp, Sqrt, Grp(D(5)), Times, Sp, v, Sp, Plus, Sp,
            remainderV, Sp, Land, Sp,
            remainderV, Sp, Eq, Sp,
            Grp(Varphi, Sp, Minus, Sp, D(1)), Sp, Minus, Sp,
            Call("fract", shiftedPhase), Sp, Land, RowBreak,
            remainderV, Sp, InMacro, Sp, remainderWindow, Sp, Land, Sp,
            gap, Sp, InMacro, Sp, twoDistances, Sp, Land, RowBreak,
            Open, gap, Sp, Eq, Sp, Varphi, Sp, Iff, Sp,
            beattyIncrement, Sp, Eq, Sp, D(1), Close,
            Close, Sp, Land, RowBreak,
            Call("beta", D(2)), Sp, Minus, Sp, Call("beta", D(1)),
            Sp, Eq, Sp, Varphi, Dot));
    }
}
