using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class DedicatedPairReplacementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A shared stationary table uses two physical reads to retain arbitrary adjacent-pair labels.",
        H("Dedicated adjacent-pair replacement"),
        Blocks(
            Paragraph(Text(
                "Let p be at least two, P at least three, and 0 <= L <= P-3. Put d=P-L-1 "
                + "and M=pP. A physical configuration is a phase in ZMod(M) and a control. "
                + "The Controller action, waitNext, readNext, output and step functions are "
                + "those of ActualControlSlots. A wait increments the full phase by one; a "
                + "read leaves it fixed and consults floor(val/P) in Fin p. A halt is absorbing.")),
            Paragraph(Text(
                "E is any finite exterior carrier, and labels:Fin p times Fin 2 -> E is any "
                + "preassigned family of terminal controls. Write O=E plus (Fin p times Fin(d+1)) "
                + "for the old carrier. Dedicated(C,labels) says that every old internal "
                + "control (b,i) with i>0 waits and moves to (b,i-1), while (b,0) reads. Its "
                + "digit b row leads to labels(b,0), and its cyclic successor digit row leads "
                + "to labels(b,1). Every such exterior label halts. The p internal chains "
                + "are disjoint, with d wait controls and one read control each. No injectivity "
                + "of the label family is required.")),
            Paragraph(Text(
                "Write I=Fin d plus (Fin p times Fin 2), and N=E plus I. The common entry "
                + "is inr(inl(d-1)); q=inr(inl(0)) is the common read. For each b, W_b is "
                + "inr(inr(b,0)) and T_b is inr(inr(b,1)). All these controls are charged in I. "
                + "The map r:O -> N fixes exterior controls and sends every old internal "
                + "control to the common entry. The configuration map J(s,u)=(s,r(u)) "
                + "retains the complete phase. The notation trajectory(C,c,n) denotes n iterates of "
                + "C.step(hp,hP) at c; trajectory(T,c,n) has the same meaning for T. In the formulas, "
                + "s(b,e)=[bP+L+val(e)]_M, z(b,e)=(s(b,e)+d,inl(labels(b,e))), and "
                + "Exterior(C,c,n) means every old control strictly before n is exterior.")),
            Paragraph(Text(
                "Follows(C,c,w,z) checks the action at each actual configuration against "
                + "the word w and ends at the complete configuration z. Proof parameters "
                + "hp and hP are suppressed in this notation. Put w=W^(d-1) R W R. "
                + "The counts below count actual wait and read symbols, respectively. "
                + "The exterior prefix premise gives the path bridge: affected paths enter "
                + "at an old dedicated entry with the prescribed phase; every other actual "
                + "path stays exterior. Thus the exclusivity assumption supplies precisely "
                + "the hypotheses of the two path clauses. The new suffix needs two reads, "
                + "so applying it within a fixed reading budget requires that allowance.")),
            Describe.Lean(DescribeId.Create("dedicated-pair-shared-table"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/Algorithms/DedicatedPairReplacement.result"),
                H("One table, all entrances, and the exterior bridge"),
                StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The common countdown uses d-1 waits and reaches q with the original "
                    + "digit b and low phase P-2 or P-1. The actual digit row chooses W_b, "
                    + "whose one wait leads to T_b. At the final phase, the digit is b for "
                    + "e=0 and the cyclic successor of b for e=1, including wraparound in "
                    + "the full source modulus. T_b therefore chooses the fixed label, and "
                    + "the run stops immediately. The first read recovers b from the source; "
                    + "no branch register or clock is supplied outside the charged carrier. "
                    + "Exterior rows preserve their actions and outputs and redirect their "
                    + "successors. Iterating this correspondence through an exterior prefix "
                    + "gives the same prefix actions. The old and new suffix endpoints then "
                    + "agree in complete phase and terminal identity, with one additional "
                    + "read in the new suffix. Every path which stays exterior is unchanged. "
                    + "The fee comparison concerns these two disjoint and shared constructions; "
                    + "strict savings hold exactly when the displayed integer difference is positive."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var exterior = All("u", V("E"), And(
            EqF(Call("action", V("T"), Inl(V("u"))), Call("action", V("C"), Inl(V("u")))),
            EqF(Call("output", V("T"), Inl(V("u"))), Call("output", V("C"), Inl(V("u")))),
            EqF(Call("waitNext", V("T"), Inl(V("u"))), Call("r", Call("waitNext", V("C"), Inl(V("u"))))),
            All("a", Fin("p"), EqF(Call("readNext", V("T"), Inl(V("u")), V("a")),
                Call("r", Call("readNext", V("C"), Inl(V("u")), V("a")))))));
        var fees = And(
            EqF(Call("NatCard", Prod(Fin("p"), Call("Fin", Add(V("d"), D(1))))), Mul(V("p"), Add(V("d"), D(1)))),
            EqF(Call("NatCard", V("I")), Add(V("d"), Mul(D(2), V("p")))),
            EqF(Call("NatCard", V("O")), Add(Call("NatCard", V("E")), Mul(V("p"), Add(V("d"), D(1))))),
            EqF(Call("NatCard", V("N")), Add(Call("NatCard", V("E")), Add(V("d"), Mul(D(2), V("p"))))),
            EqF(Sub(Mul(V("p"), Add(V("d"), D(1))), Add(V("d"), Mul(D(2), V("p")))),
                Sub(Mul(Sub(V("p"), D(1)), V("d")), V("p"))),
            IffF(LT(Add(V("d"), Mul(D(2), V("p"))), Mul(V("p"), Add(V("d"), D(1)))),
                LT(D(0), Sub(Mul(Sub(V("p"), D(1)), V("d")), V("p")))));
        var localRun = All("b", Fin("p"), All("e", Call("Fin", D(2)), And(
            Call("Follows", V("T"), Pair(Call("s", V("b"), V("e")), V("entry")),
                Call("replicate", Sub(V("d"), D(1)), V("W")), Pair(Add(Call("s", V("b"), V("e")), Sub(V("d"), D(1))), V("q"))),
            EqF(Call("digit", Add(Call("s", V("b"), V("e")), Sub(V("d"), D(1)))), V("b")),
            EqF(Call("action", V("T"), V("q")), V("R")),
            EqF(Call("readNext", V("T"), V("q"), V("b")), Call("W", V("b"))),
            EqF(Call("action", V("T"), Call("W", V("b"))), V("W")),
            EqF(Call("waitNext", V("T"), Call("W", V("b"))), Call("T", V("b"))),
            EqF(Call("action", V("T"), Call("T", V("b"))), V("R")),
            Call("Follows", V("T"), Pair(Call("s", V("b"), V("e")), V("entry")), V("w"), End()),
            EqF(Iter("T", Pair(Call("s", V("b"), V("e")), V("entry")), Add(V("d"), D(2))), End()),
            All("i", N, Imp(LT(V("i"), Add(V("d"), D(2))),
                Ne(Call("action", V("T"), Call("snd", Iter("T", Pair(Call("s", V("b"), V("e")), V("entry")), V("i")))), V("halt")))),
            EqF(Call("action", V("T"), Label()), V("halt")),
            EqF(Call("output", V("T"), Label()), Call("output", V("C"), Label())))));
        var prefix = All("c", Prod(Source, V("O")), All("n", N,
            Imp(Call("Exterior", V("C"), V("c"), V("n")), And(
                EqF(Iter("T", Call("J", V("c")), V("n")), Call("J", Iter("C", V("c"), V("n")))),
                All("i", N, Imp(LT(V("i"), V("n")), EqF(
                    Call("action", V("T"), Call("snd", Iter("T", Call("J", V("c")), V("i")))),
                    Call("action", V("C"), Call("snd", Iter("C", V("c"), V("i")))))))))));
        var affected = All("c", Prod(Source, V("O")), All("n", N,
            All("b", Fin("p"), All("e", Call("Fin", D(2)),
                Imp(Call("Exterior", V("C"), V("c"), V("n")), Imp(
                    EqF(Iter("C", V("c"), V("n")), Pair(Call("s", V("b"), V("e")), Inr(Pair(V("b"), V("d"))))),
                    And(
                        EqF(Iter("C", V("c"), Add(V("n"), Add(V("d"), D(1)))), End()),
                        EqF(Iter("T", Call("J", V("c")), Add(V("n"), Add(V("d"), D(2)))), End()),
                        EqF(Call("output", V("C"), Call("snd", Iter("C", V("c"), Add(V("n"), Add(V("d"), D(1)))))),
                            Call("output", V("T"), Call("snd", Iter("T", Call("J", V("c")), Add(V("n"), Add(V("d"), D(2))))))))))))));
        var body = And(
            EqF(Call("initial", V("T")), Call("r", Call("initial", V("C")))),
            exterior, fees,
            EqF(Call("waitCount", V("w")), V("d")), EqF(Call("readCount", V("w")), D(2)),
            localRun, prefix, affected);
        return All("p", N, All("P", N, All("L", N,
            Imp(And(LE(D(2), V("p")), LE(D(3), V("P")), LE(V("L"), Sub(V("P"), D(3)))),
                All("E", V("Type"), Imp(Call("Finite", V("E")),
                    All("labels", Seq(Prod(Fin("p"), Call("Fin", D(2))), To, V("E")),
                        All("C", Call("Controller", V("p"), V("P"), V("O")),
                            Imp(Call("Dedicated", V("C"), V("labels")),
                                Ex("T", Call("Controller", V("p"), V("P"), V("N")), body))))))))));
    }

    private static Formula N => Seq(Mathbb, Sp, Grp(V("N")));
    private static Formula Source => Call("ZMod", Mul(V("p"), V("P")));
    private static Formula Fin(string n) => Call("Fin", V(n));
    private static Formula V(string s) => F.Id(s);
    private static Formula Iter(string table, Formula c, Formula n) => Call("trajectory", V(table), c, n);
    private static Formula Label() => Inl(Call("labels", Pair(V("b"), V("e"))));
    private static Formula End() => Pair(Add(Call("s", V("b"), V("e")), V("d")), Label());
    private static Formula Inl(Formula f) => Call("inl", f);
    private static Formula Inr(Formula f) => Call("inr", f);
    private static Formula Pair(Formula a, Formula b) => Seq(Open, a, Comma, b, Close);
    private static Formula Prod(Formula a, Formula b) => Seq(Grp(a), Times, Sp, Grp(b));
    private static Formula Mul(Formula a, Formula b) => Prod(a, b);
    private static Formula EqF(Formula a, Formula b) => Seq(Grp(a), Eq, Grp(b));
    private static Formula Ne(Formula a, Formula b) => Seq(Grp(a), Neq, Sp, Grp(b));
    private static Formula LE(Formula a, Formula b) => Seq(Grp(a), Le, Sp, Grp(b));
    private static Formula LT(Formula a, Formula b) => Seq(Grp(a), Lt, Grp(b));
    private static Formula Sub(Formula a, Formula b) => Seq(Grp(a), Minus, Grp(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Grp(a), Implies, Grp(b));
    private static Formula IffF(Formula a, Formula b) => Seq(Grp(a), Iff, Grp(b));
    private static Formula All(string s, Formula type, Formula body) =>
        Seq(Forall, Sp, V(s), Colon, type, Comma, Grp(body));
    private static Formula Ex(string s, Formula type, Formula body) =>
        Seq(Exists, Sp, V(s), Colon, type, Comma, Grp(body));
    private static Formula Join(Formula separator, Formula[] args) =>
        Seq([.. args.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { separator, x })]);
    private static Formula Add(params Formula[] args) => Join(Plus, args);
    private static Formula And(params Formula[] args) => Join(Land, [.. args.Select(x => Grp(x))]);
    private static Formula Call(string s, params Formula[] args) =>
        Seq(Operatorname, Sp, Grp(V(s)), Open, Join(Comma, args), Close);
}
