using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Budget;

internal sealed class TerminalClockCompressionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A known dyadic sensor protocol admits exact decoding from its final phase and bit, with a sharp bound on attained clock labels.",
        H("Terminal Clock Compression"),
        Blocks(
            Paragraph(Text(
                "Let d be a natural number, P=2^(d+1), and b a known bit. Protocol(d+1) is the binary controller type: each node waits a finite natural number of events and selects its continuation from the acquired raw bit. Correct(p) means that execution from time zero returns r for every r<P, using at most d+1 queries. The raw sensor reads floor((bP+r+n)/P) modulo two. These are the same controllers and sensors used for dyadic forward waiting.")),
            Paragraph(Text(
                "For a fixed controller p and initial bit b, let N(r) be the time of its final query, S(r)=N(r) mod P, Y(r) its final raw bit, and T(r)=(S(r),Y(r)). Put R={r in N : r<P}, O={(s,y) in N x Fin(2) : s<P and s mod 2=1}, and c(t)=floor(N(2t)/P). Define a(s)=floor((P-1-s)/2) and D(s,y)=2a(s)+(y+b+c(a(s))) mod 2. The plus signs in the correction equal subtraction modulo two.")),
            Paragraph(Text(
                "For a clock summary phi:N->Z, let L(phi)={phi(N(r)):r in R}; only attained labels are counted. Write phase(P) for the map n->n mod P. The decoder knows p and b. Its bound counts neither the description of p, the computation of c, nor storage during acquisition. The record T contains the phase latched at the final query; an elapsed-time variable that is not part of the record cannot be used in this decoding relation.")),
            Describe.Lean(
                DescribeId.Create("terminal-pair-fiber-bijection-and-clock-injectivity"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Budget/TerminalClockCompression.terminal_pair_fiber_bijection_and_clock_injectivity"),
                H("The exact terminal encoding and attained clock bound"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Capacity saturation forces midpoint cuts. Induction through the threshold tree gives a common final-query time for each adjacent pair and forces its terminal phase. The final bit recovers the remaining source bit after correction. Choosing a source with final bit zero in every pair forces distinct clock labels for distinct pair indices."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "Let early be the raw-bit version of the earliest midpoint controller: at every interval it waits for the first forward occurrence of the midpoint phase. Write N_early and c_early for its completion time and period quotient, and wt(t) for the number of ones in the binary expansion of t. Since t<2^d, this is also its d-bit binary weight. The following identity makes the period correction computable from the recovered t.")),
            Describe.Lean(
                DescribeId.Create("earliest-midpoint-terminal-time"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Budget/TerminalClockCompression.earliest_midpoint_terminal_time"),
                H("Earliest midpoint completion time"),
                StatementSource.FromAuthor(EarliestStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Induction on the remaining depth tracks the exact waiting increments. The upper-half branch adds one binary digit of value one and one complete period to the time identity. Division by P leaves the binary weight because the remaining phase lies between zero and P."))),
                DescribeRole.Theorem))));

    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Eqn(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula LtN(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula LeqN(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula And(params Formula[] xs) => xs.Reverse().Aggregate((a, b) => new Formula.Logic(b, FormulaLogicOperator.And, a));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Arrow(Formula x, Formula y) => new Formula.TypeArrow(x, y);
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Statement()
    {
        var d = F.Id("d"); var b = F.Id("b"); var p = F.Id("p"); var t = F.Id("t");
        var u = F.Id("u"); var r = F.Id("r"); var P = F.Id("P"); var Z = F.Id("Z");
        var phi = F.Id("phi"); var recover = F.Id("recover");
        var phase = Call("S", r); var bit = Call("Y", r);
        var evenSource = Mul(D(2), t);
        var sourcePair = Add(evenSource, u);
        var phaseLaw = Eqn(Call("N", evenSource), Call("N", Add(evenSource, D(1))));
        var oddPhase = Eqn(Call("S", evenSource), Sub(Sub(P, D(1)), evenSource));
        var bitLaw = Eqn(Call("Y", sourcePair), Call("mod", Add(Add(b, Call("c", t)), u), D(2)));
        var pairLaw = All("t", Nats(), Imp(LtN(t, Pow(D(2), d)), And(phaseLaw, oddPhase,
            All("u", Nats(), Imp(LtN(u, D(2)), bitLaw)))));
        var inverse = All("r", Nats(), Imp(LtN(r, P), Eqn(Call("D", phase, bit), r)));
        var labels = Eqn(Call("card", Call("L", Call("phase", P))), Pow(D(2), d));
        var recovery = All("r", Nats(), Imp(LtN(r, P),
            Eqn(Call("recover", Call("phi", Call("N", r)), Call("Y", r)), r)));
        var lower = All("Z", F.Id("Type"), All("phi", Arrow(Nats(), Z),
            All("recover", Arrow(Z, Arrow(Call("Fin", D(2)), Nats())),
                Imp(recovery, LeqN(Pow(D(2), d), Call("card", Call("L", phi)))))));
        var body = Imp(Call("Correct", p), And(pairLaw, inverse,
            Call("BijOn", F.Id("T"), F.Id("R"), F.Id("O")), labels, lower));
        return Disp(All("d", Nats(), All("b", Call("Fin", D(2)),
            All("P", Nats(), Imp(Eqn(P, Pow(D(2), Add(d, D(1)))),
                All("p", Call("Protocol", Add(d, D(1))), body))))));
    }

    private static Formula EarliestStatement()
    {
        var d = F.Id("d"); var b = F.Id("b"); var t = F.Id("t"); var u = F.Id("u"); var P = F.Id("P");
        var weight = Call("wt", t);
        var time = Eqn(Call("Nearly", Add(Mul(D(2), t), u)), Sub(Add(Sub(P, D(1)), Mul(P, weight)), Mul(D(2), t)));
        var body = Imp(And(LtN(t, Pow(D(2), d)), LtN(u, D(2))), And(time, Eqn(Call("cearly", t), weight)));
        return Disp(All("d", Nats(), All("b", Call("Fin", D(2)), All("P", Nats(),
            Imp(Eqn(P, Pow(D(2), Add(d, D(1)))), All("t", Nats(), All("u", Nats(), body)))))));
    }
}
