using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Prediction;

internal sealed class OneSidedPredictorMinimumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp one-sided predictive memory.", H("Sharp one-sided predictive memory"), Blocks(
            Describe.Lean(DescribeId.Create("sharp-predictor-minimum"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/Prediction/OneSidedPredictorMinimum.sharp_predictor_minimum"),
                H("Sharp one-sided predictive memory"), StatementSource.FromAuthor(Disp(SharpFormula())), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("A predictor has one fixed initial state, a total update receiving one Boolean outcome, and an output in the closed interval from zero to one. Its reached state is the left-to-right runWord fold. Every persistent counter, program phase and parse state belongs to this carrier; no time or source-state argument is supplied.")),
                    Paragraph(Text("Let x lie in (0,1], let epsilon be nonnegative with 2 epsilon < x, and let p be a nonnegative decreasing sequence bounded above by x and tending to zero. The history law is x once a false outcome has occurred, and otherwise p evaluated at the history length. Correctness requires absolute next-outcome error at most epsilon for every finite Boolean history, including the empty history.")),
                    Paragraph(Text("Suppose N is the first nonstrict threshold: p(n) <= 2 epsilon if and only if N <= n. There is a correct predictor on Fin(N+1) + Unit, whose cardinality is N+2, and every correct predictor on any finite carrier has at least N+2 states.")),
                    Paragraph(Text("The Fin states store the all-one depth up to N. The last one saturates and outputs p(N)/2; the Unit state records that a zero has occurred and outputs x. The saturation error is at most p(N)/2. This includes N=0 and exact threshold equality.")),
                    Paragraph(Text("If two distinct all-one depths reach the same state, deterministic continuation repeats the earlier state along an unbounded arithmetic progression. Taking the limit of its error inequality forces the earlier p value to be at most 2 epsilon. Thus the first N+1 all-one states are distinct. A zero-history state cannot equal any of them: a common all-one suffix would require one output to approximate both x and a sequence tending to zero.")),
                    Paragraph(Text("This theorem concerns a specified history law. Applying it to a retained quantum instrument requires deriving that law from the actual branches. It counts persistent states; output installation precision and computation time are separate resources."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exact-prediction-impossible"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/Prediction/OneSidedPredictorMinimum.exact_prediction_impossible"),
                H("Exact prediction needs infinitely many states"),
                StatementSource.FromAuthor(Disp(ExactFormula())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If every p(n) is strictly positive and p tends to zero, every finite carrier fails exact all-history prediction, for any reset output x. Pigeonhole gives a repeated all-one state; its deterministic recurrence and the limit force the earlier strictly positive p value to be zero."))),
                DescribeRole.Theorem))));

    private static Formula SharpFormula()
    {
        Formula x = X("x"), e = X("e"), p = X("p"), n = X("n"), N = X("N");
        Formula carrier = Call("Sum", Call("Fin", Add(N, D(1))), C("Unit"));
        Formula correct = Call("Correct", X("M"), x, p, e);
        Formula hypotheses = Conj(LT(D(0), x), LE(x, D(1)), LE(D(0), e), LT(Mul(D(2), e), x),
            All("n", NatType(), LE(D(0), At(p, n))),
            All("n", NatType(), LE(At(p, n), x)), Call("Antitone", p),
            Call("Tendsto", p, C("atTop"), Call("nhds", D(0))),
            All("n", NatType(), IffOf(LE(At(p, n), Mul(D(2), e)), LE(N, n))));
        Formula conclusion = Conj(Some("M", Call("Predictor", carrier), correct),
            Equal(Call("card", carrier), Add(N, D(2))),
            FinitePredictors(Imp(correct, LE(Add(N, D(2)), Call("card", X("S"))))));
        return All("x", RealType(), All("e", RealType(),
            All("p", new Formula.TypeArrow(NatType(), RealType()),
                All("N", NatType(), Imp(hypotheses, conclusion)))));
    }

    private static Formula ExactFormula() => All("x", RealType(),
        All("p", new Formula.TypeArrow(NatType(), RealType()),
            Imp(Conj(All("n", NatType(), LT(D(0), At(X("p"), X("n")))),
                    Call("Tendsto", X("p"), C("atTop"), Call("nhds", D(0)))),
                FinitePredictors(new Formula.Not(Call("Correct", X("M"), X("x"), X("p"), D(0)))))));

    private static Formula X(string name) => new Formula.Symbol(FormulaIdentifier.Create(name));
    private static Formula C(string name) => new Formula.NamedConstant(FormulaIdentifier.Create(name));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(C(name), [.. args]);
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Equal(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula LE(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula LT(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThan, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) => new Formula.Logic(a, op, b);
    private static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula IffOf(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Conj(params Formula[] items)
    {
        Formula value = items[^1];
        for (var i = items.Length - 2; i >= 0; --i)
            value = Logic(items[i], FormulaLogicOperator.And, value);
        return value;
    }
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula NatType() => Seq(Mathbb, Grp(FormulaDsl.Id("N")));
    private static Formula RealType() => Seq(Mathbb, Grp(FormulaDsl.Id("R")));
    private static Formula FinitePredictors(Formula body) => All("S", C("Type"),
        All("inst", Call("Fintype", X("S")), All("M", Call("Predictor", X("S")), body)));
}
