using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.DBonacci;

internal sealed class DBonacciTerminalSamplingLawDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var m = Id("m"); var f = Id("f"); var h = Id("h"); var c = Id("c");
        var w = Id("w"); var q = Id("q"); var t = Id("t"); var x = Id("x"); var n = Id("N");
        Formula All(string name, Formula domain, Formula body) =>
            new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
        Formula Mass(Formula set) => Call("mu", set);
        Formula Return(Formula fuel, Formula length, Formula cursor) => Call("Return", m, fuel, length, cursor, w);
        Formula UniversalWord(Formula body) => All("f", Id("Nat"), All("h", Id("Nat"),
            All("c", Id("Nat"), All("w", Call("Words", h), body))));
        var d = Call("C", m, f, Add(q, Num(1)));
        var draw = Call("Draw", Add(q, Num(1)), d, c, t, x);
        var next = Call("if", Call("AtLeast", x, Call("C", m, m, q)), Subtract(f, Num(1)), m);
        var stop = Add(c, Multiply(Add(t, Num(1)), Add(q, Num(1))));
        var continuation = Return(next, q, stop);
        var statement = All("m", Id("Nat"), new Formula.Aligned([
            UniversalWord(Equal(Mass(Return(f,h,c)),
                Call("if", Call("Legal", m,f,h,w), new Formula.Fraction(Num(1), Call("C",m,f,h)), Num(0)))),
            UniversalWord(Equal(Mass(Return(f,h,c)), Call("ConditionalFairWordMass", m,f,h,w))),
            All("f", Id("Nat"), All("q", Id("Nat"), All("c", Id("Nat"), All("t", Id("Nat"),
                All("x", Call("Fin", new Formula.Power(Num(2), Add(q,Num(1)))), All("w", Call("Words",q),
                    Equal(Mass(Call("Intersection", draw, continuation)), Multiply(Mass(draw), Mass(continuation))))))))),
            All("N", Id("Nat"), All("c", Id("Nat"), All("w", Call("Words",n),
                Equal(Mass(Return(m,n,c)), Call("if", Call("Legal",m,m,n,w),
                    new Formula.Fraction(Num(1), Call("dbonacci", Add(m,Num(1)), Add(n,Num(2)))), Num(0))))))
        ]));
        return DocumentDefinition.Create(ScribeNode.Create(
        "Adaptive first-hit fair-bit sampling is uniform on native legal terminal words.",
        H("Uniform Legal Terminal Law"),
        Blocks(
            Paragraph(Text(
                "For each native live state, CompletionCount counts literal legal completions "
                + "of the remaining actual output length. The empty layer has one word. The "
                + "next false branch has count C(maxTrue,q); a true branch, when fuel is positive, "
                + "has count C(fuel-1,q). Their sum is the current count. With zero fuel the "
                + "true branch is forbidden.")),
            Describe.Lean(
                DescribeId.Create("adaptive-fair-tape-uniform-native-law"),
                DeclarationHandle.Create(
                    "D5/S0/Tower/DBonacci/TerminalSamplingLaw.terminal_sampling_uniform_law"),
                H("Adaptive composition and the uniform completion law"),
                StatementSource.FromAuthor(statement),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At every fixed first-accepted draw (t,x), the consumed cursor is "
                        + "cursor+(t+1)(q+1). Its event depends only on the finite source prefix "
                        + "before that cursor. Native replay identifies the continuation event "
                        + "with an event of the unused suffix. Independence of these disjoint "
                        + "iid coordinate families proves exact event factorization on the same tape.")),
                    Paragraph(Text(
                        "Nat denotes natural numbers, Words(h) is Fin h to Bool, C(m,f,h) is "
                        + "completionCount and mu is fairTape. Return is the event that sample "
                        + "returns the displayed word with some finite final cursor. Draw fixes "
                        + "the first accepted retry and integer. Legal is native runAdmissible=true. "
                        + "ConditionalFairWordMass is the mass of the singleton word under the "
                        + "iid fair Fin h word measure conditioned on that native legal set. "
                        + "AtLeast compares integer values; subtraction is natural subtraction. "
                        + "The four displayed rows hold jointly, for every listed parameter.")),
                    Paragraph(Text(
                        "A returned-word event is the disjoint union over accepted branch "
                        + "integers and retry indices of the corresponding draw-and-continuation "
                        + "events. Summing over retries gives integer mass 1/C. There are exactly "
                        + "C(next) accepted integers selecting the requested next bit. Induction "
                        + "on the remaining output length cancels C(next) against the continuation "
                        + "mass 1/C(next). The resulting path mass is 1/C(initial), including the "
                        + "empty terminal word and forced-zero branches.")),
                    Paragraph(Text(
                        "For maxTrue=k-1 and initial fuel=k-1, the native full-budget count is "
                        + "dbonacci k (N+2). Every legal length-N word therefore has mass 1/G_N, "
                        + "and every illegal word has mass zero. The same returned-word law equals "
                        + "the iid fair length-N word law conditioned on native legality. All branch "
                        + "choices use the concrete fair-bit rejection evaluator; infinite retries "
                        + "are exceptional. The state retains N's remaining output budget and "
                        + "does not define a stationary law on tail state alone."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Tower/DBonacci/TerminalSampling"))]));
    }
}
