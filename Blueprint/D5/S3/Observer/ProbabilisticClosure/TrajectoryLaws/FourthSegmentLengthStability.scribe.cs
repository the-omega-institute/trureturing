using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class FourthSegmentLengthStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula r = F.Id("r"), s = F.Id("s"), j = F.Id("j"), t = F.Id("t");
        Formula k = F.Id("k"), l = F.Id("l"), n = F.Id("n");
        Formula real = F.Id("Real"), nat = F.Id("Nat"), unit = F.Id("unitInterval");
        Formula depth = F.Id("Depth");
        Formula rateR = Call("rate", k), rateS = Call("rate", Add(k, D(1)));
        Formula xi = Mul(r, Sub(D(1), r));
        Formula derivativeTerm = Add(Abs(Call("deriv", Call("A", j), r)),
            Abs(Call("deriv", Call("B", j), r)));
        Formula atomClauses = And(
            Equal(Call("nativeLengthPushforward", r), Call("D", r)),
            Equal(Call("noncompletionMass", r), D(0)),
            Equal(Call("mass", Call("D", r), F.Id("none")), D(0)),
            Equal(Call("mass", Call("D", r), Call("some", D(0))), D(0)),
            All("j", nat, And(
                Equal(Call("realMass", Call("D", r), Call("some", Add(Mul(D(2), j), D(1)))),
                    Mul(r, Pow(xi, j))),
                Equal(Call("realMass", Call("D", r), Call("some", Add(Mul(D(2), j), D(2)))),
                    Mul(Pow(Sub(D(1), r), D(2)), Pow(xi, j))))));
        Formula budget = All("r", real, Imp(InInterval(r), And(
            Call("Summable", Call("coordinateDerivative", r)),
            Seq(Mul(Fraction(D(1), D(2)), Call("tsum", Call("coordinateDerivative", r))), Le,
                Fraction(Mul(D(2), Sub(D(1), r)), Sub(D(1), xi))),
            Seq(Fraction(Mul(D(2), Sub(D(1), r)), Sub(D(1), xi)), Le,
                Fraction(D(1,2), D(7))))));
        Formula continuity = All("r", unit, All("s", unit,
            Imp(And(InInterval(r), InInterval(s)),
                Seq(Tv(Call("D", r), Call("D", s)), Le,
                    Call("ofReal", Mul(Fraction(D(1,2), D(7)), Abs(Sub(r, s))))))));
        Formula adjacent = All("k", depth, And(
            Equal(Abs(Sub(rateR, rateS)),
                Fraction(D(1), Mul(Fib(Add(k, D(3))), Fib(Add(k, D(4)))))),
            Seq(Tv(Call("D", rateR), Call("D", rateS)), Le,
                Call("ofReal", Fraction(D(1,2),
                    Mul(Mul(D(7), Fib(Add(k, D(3)))), Fib(Add(k, D(4)))))))));
        Formula convergence = Call("Tendsto", F.Id("adjacentLengthTV"),
            F.Id("atTop"), Call("nhds", D(0)));
        Formula separation = All("k", depth, All("l", depth,
            Imp(Seq(k, Neq, Sp, l), Equal(Tv(Call("dirac", k), Call("dirac", l)), D(1)))));
        Formula boundConvergence = Call("Tendsto", F.Id("adjacentFibonacciBound"),
            F.Id("atTop"), Call("nhds", D(0)));
        Formula statement = And(All("r", unit, atomClauses), budget, continuity,
            adjacent, boundConvergence, convergence, separation);
        return DocumentDefinition.Create(ScribeNode.Create(
            "The complete original phase-p length law is uniformly continuous while distinct deterministic depths remain separated.",
            H("Stopped-length continuity and deterministic depth separation"), Blocks(
                Paragraph(Text("D(r) denotes the existing explicitStoppedWordLaw(p,r) pushed through lengthProjection. nativeLengthPushforward(r) is rawReadLaw(r) pushed through the actual stoppedReadWord(p) followed by lengthProjection. noncompletionMass(r) is rawReadLaw(r) of the event stoppedReadWord(p)=none. The output carrier remains Option Nat: none is infinite noncompletion, and some zero is an impossible finite length. realMass is the real value of the indicated singleton measure; mass retains its extended nonnegative real value.")),
                Paragraph(Text("For every real t and natural j, A(j) and B(j) are the polynomial coordinate extensions below. Their values at a unit-interval parameter are the complete odd and even singleton masses. coordinateDerivative(r)(j) is the sum of the two absolute derivatives, so its series includes every positive length exactly once.")),
                new DocumentBlock.DisplayFormula(All("j", nat, All("t", real, And(
                    Equal(Call("A", j, t), Mul(t, Pow(Mul(t, Sub(D(1), t)), j))),
                    Equal(Call("B", j, t), Mul(Pow(Sub(D(1), t), D(2)),
                        Pow(Mul(t, Sub(D(1), t)), j))))))),
                new DocumentBlock.DisplayFormula(All("r", real, All("j", nat,
                    Equal(Call("coordinateDerivative", r, j), derivativeTerm)))),
                Paragraph(Text("TV is the existing measurableTotalVariation: the supremum of the larger of the two directed event-mass gaps over all measurable events. It takes extended nonnegative real values. ofReal embeds a real bound in that carrier. Depth is the original positive natural depth carrier, and rate(k)=fib(k+1)/fib(k+3). The addition k+1 in the display means the positive depth with that natural value; fib uses F(0)=0 and F(1)=1.")),
                new DocumentBlock.DisplayFormula(All("n", nat,
                    Equal(Call("adjacentLengthTV", n),
                        Tv(Call("D", Call("rate", Add(n, D(1)))),
                            Call("D", Call("rate", Add(n, D(2)))))))),
                new DocumentBlock.DisplayFormula(All("n", nat,
                    Equal(Call("adjacentFibonacciBound", n), Call("ofReal",
                        Fraction(D(1,2), Mul(Mul(D(7), Fib(Add(n, D(4)))),
                            Fib(Add(n, D(5))))))))),
                Describe.Lean(DescribeId.Create("original-stopped-length-stability"),
                    DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentLengthStability.original_stopped_length_stability"),
                    H("The full quantitative law"), StatementSource.FromAuthor(Disp(statement)),
                    AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("The native stopped-word theorem supplies the original parser pushforward and proves zero mass of infinite noncompletion. The existing length projection and its all-index atom identities give the two complete coordinate families; no completion conditioning or finite cutoff is used.")),
                        Paragraph(Text("Differentiating each polynomial coordinate gives an absolutely summable family. The geometric series and its weighted derivative series bound half its absolute derivative sum by 2(1-r)/(1-r(1-r)), which is at most 12/7 throughout the closed interval [1/3,2/5]. The endpoint cases are included.")),
                        Paragraph(Text("For ordered r at most s, the original stopped-word measures share a submeasure with odd weights r xi(r)^j and even weights (1-s)^2 xi(r)^j. Its total mass is (r+(1-s)^2)/(1-xi(r)). The event-supremum distance is at most the missing common mass, hence at most (s-r)(2-r-s)/(1-xi(r)), and therefore at most (12/7)(s-r). Symmetry covers the reverse order, including r=s, and measurable length projection contracts TV.")),
                        Paragraph(Text("Vajda's Fibonacci identity gives the exact adjacent response-rate gap. The quantitative estimate applies to every positive depth; reciprocal Fibonacci products converge to zero, so the full adjacent output-law distances converge to zero. The singleton event at either of two distinct positive depths gives Dirac-law distance one.")),
                        Paragraph(Text("These are different deterministic-depth sources. This result does not assert the stronger theorem about actual histories under one fixed installed prior. Exact length-law recovery is compatible with the loss of a uniform inverse stability estimate across unbounded deterministic source depths."))),
                    DescribeRole.Theorem))));
    }
    private static Formula Seq(params Formula[] xs) => F.Seq(xs);
    private static Formula Equal(Formula a, Formula b) => Seq(a, Eq, b);
    private static Formula Add(Formula a, Formula b) => Seq(Open, a, Plus, b, Close);
    private static Formula Sub(Formula a, Formula b) => Seq(Open, a, Minus, b, Close);
    private static Formula Mul(Formula a, Formula b) => Seq(Open, a, Close, Star, Open, b, Close);
    private static Formula Pow(Formula a, Formula b) => Seq(Grp(Seq(Open, a, Close)), Caret, Grp(b));
    private static Formula Fraction(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Abs(Formula a) => Seq(Lvert, Sp, a, Rvert, Sp);
    private static Formula Fib(Formula a) => Call("fib", a);
    private static Formula Tv(Formula a, Formula b) => Call("TV", a, b);
    private static Formula InInterval(Formula a) => Seq(a, InMacro, Sp, OpenBracket,
        Fraction(D(1), D(3)), Comma, Fraction(D(2), D(5)), CloseBracket);
    private static Formula Imp(Formula p, Formula q) => Seq(Open, p, Close, Rightarrow, Open, q, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, type, Comma, Sp, Open, body, Close);
    private static Formula And(params Formula[] xs)
    {
        var parts = new Formula[xs.Length * 2 - 1];
        for (var i = 0; i < xs.Length; i++)
        {
            parts[i * 2] = Seq(Open, xs[i], Close);
            if (i > 0) parts[i * 2 - 1] = Seq(Land, Sp);
        }
        return Seq(parts);
    }
    private static Formula Call(string name, params Formula[] xs)
    {
        var parts = new Formula[xs.Length * 2 - 1];
        for (var i = 0; i < xs.Length; i++)
        {
            parts[i * 2] = xs[i];
            if (i > 0) parts[i * 2 - 1] = Comma;
        }
        return Seq(Operatorname, Grp(F.Id(name)), Open, Seq(parts), Close);
    }
}
