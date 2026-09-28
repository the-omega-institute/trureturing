using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Prediction;

internal sealed class DelayedPulseMemoryGapDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/ObserverMemory/Prediction/DelayedPulseMemoryGap.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Delayed pulses have exact static and all-time finite-memory minima.",
        H("Delayed Pulse Memory Gap"),
        Blocks(
            Paragraph(Text("Let m and H be natural numbers. The source state n advances to n+1, and its real output o_m(n) is one when n=m and zero otherwise. Let 0 <= epsilon < 1/2. All correctness conditions quantify over every initial n, and times include zero.")),
            Describe.Lean(
                DescribeId.Create("delayed-pulse-memory-gap"),
                DeclarationHandle.Create(Owner + "delayed_pulse_memory_gap"),
                H("Exact static and all-time memory minima"),
                StatementSource.FromAuthor(MinimaFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("StaticCorrect(m,H,epsilon,e,D) means that |D(e(n),t)-o_m(n+t)| <= epsilon for every n and every t <= H. The set staticSizes consists of card(C) for finite types C admitting such an encoder e and decoder D. There is no requirement to update a static label.")),
                    Paragraph(Text("Write K=min(H,m). The attaining carrier is Fin(K+2). The encoder stores m-n when n <= m and m-n <= H; otherwise it stores K+1. The decoder outputs one precisely when its label equals t and t <= K. This reproduces every window response exactly.")),
                    Paragraph(Text("For each j from zero through K, the initial state m-j produces a pulse at window time j. The initial state m+1 gives the silent response. Any two of these K+2 responses differ by one at a window time, so their labels cannot coincide: a shared real prediction would force 1 <= 2 epsilon. Injectivity gives the lower bound.")),
                    Paragraph(Text("UpdaterCorrect(m,epsilon,e,U,r) means that |r(U^[t](e(n)))-o_m(n+t)| <= epsilon for every n and every natural time t. The set updaterSizes consists of card(Q) for finite types Q admitting one fixed encoder, update and readout satisfying this condition.")),
                    Paragraph(Text("The attaining carrier is Fin(m+2). Encode n as min(n,m+1), update q to min(q+1,m+1), and output one exactly at state m. The state m+1 is absorbing. Induction gives the exact invariant U^[t](e(n))=min(n+t,m+1), hence exact outputs at every time.")),
                    Paragraph(Text("For any initial states i<j among zero through m+1, continue for m-i steps. The output from i is one and the output from j is zero. If their encodings agreed, the updater would give the same prediction at this time, again contradicting epsilon < 1/2. Thus all m+2 encodings must be distinct.")),
                    Paragraph(Text("Both minima include m=0 and epsilon=0; the static result also includes H=0. Keeping H fixed and increasing m makes the difference between the two minimum counts arbitrarily large."))),
                DescribeRole.Theorem))));

    private static Formula MinimaFormula() => Disp(Seq(
        Begin, Grp(F.Id("gathered")),
        Forall, Sp, F.Id("m"), Comma, F.Id("H"), InMacro, Nat, Comma, Sp,
        Forall, Sp, Eps, InMacro, Real, Comma, Sp,
        D(0), Leq, Eps, Lt, Frac, Grp(D(1)), Grp(D(2)), Rightarrow, RowBreak,
        Call("StaticCorrect", F.Id("m"), F.Id("H"), Eps,
            Call("staticEncode", F.Id("m"), F.Id("H")),
            Call("staticDecode", F.Id("m"), F.Id("H"))), Land, RowBreak,
        Call("IsLeast", Call("staticSizes", F.Id("m"), F.Id("H"), Eps),
            Seq(Call("min", F.Id("H"), F.Id("m")), Plus, D(2))), Land, RowBreak,
        Call("UpdaterCorrect", F.Id("m"), Eps,
            Call("machineEncode", F.Id("m")), Call("machineUpdate", F.Id("m")),
            Call("machineReadout", F.Id("m"))), Land, RowBreak,
        Call("IsLeast", Call("updaterSizes", F.Id("m"), Eps),
            Seq(F.Id("m"), Plus, D(2))),
        End, Grp(F.Id("gathered"))));

    private static Formula Eps => Varepsilon;
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[i]);
        }
        items.Add(Close);
        return Seq(items.ToArray());
    }
}
