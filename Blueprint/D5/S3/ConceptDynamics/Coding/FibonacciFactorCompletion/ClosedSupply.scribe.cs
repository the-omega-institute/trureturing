using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion;

internal sealed class ClosedSupplyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ClosedSupply.";
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula And(params Formula[] clauses)
    {
        var result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; --i)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula I(string name) => F.Id(name);
    private static Formula Returns => Call("List", I("Return"));
    private static Formula Add(Formula a, Formula b) => Call("add", a, b);
    private static Formula Sub(Formula a, Formula b) => Call("subtract", a, b);
    private static Formula Mul(Formula a, Formula b) => Call("multiply", a, b);
    private static Formula Pow(Formula a, Formula b) => Call("power", a, b);

    private static Formula ClosedRecordSupply()
    {
        var model = I("model"); var o = I("o"); var b = I("b");
        var xs = I("execution"); var k = I("K"); var high = I("high");
        var h = Call("hSide", high); var a = Call("aSide", high);
        var ck = Pow(I("chi"), k); var g2 = Pow(I("g"), D(2));
        var z = Call("divide", a, Sub(D(1), Mul(I("rho"), ck)));
        var q = Sub(I("lam"), Mul(Mul(g2, ck), h));
        var psi = Sub(I("lam"), Mul(Mul(g2, ck), z));
        var d = Call("divide", Call("divide", Sub(I("lam"), b), g2), ck);
        var trace = Call("GuardTrace", k, d, Call("boolNot", Call("apply", o, D(0))), high, xs,
            Call("initial", high, model));
        Formula Supply(string contract) => Call("ActualPairSupply", model, o, b, I(contract), xs);
        Formula Iff(Formula x, Formula y) => And(
            new Formula.Logic(x, FormulaLogicOperator.Implies, y),
            new Formula.Logic(y, FormulaLogicOperator.Implies, x));
        return Disp(All(new Formula.Logic(
            And(Call("le", D(2), k), Call("lt", q, b), Call("lt", b, psi)),
            FormulaLogicOperator.Implies,
            Iff(Supply("closed"), trace)),
            B("model", I("Model")), B("o", I("Ownership")), B("b", I("Real")),
            B("execution", Returns), B("K", I("Nat"))));
    }

    private static Formula ResetFirstReturn()
    {
        var o = I("o"); var b = I("b"); var k = I("K"); var high = I("high");
        var reset = I("R"); var rm = Call("m", reset); var xs = I("xs");
        var h = Call("hSide", high); var a = Call("aSide", high);
        var ck = Pow(I("chi"), k); var g2 = Pow(I("g"), D(2));
        var d = Call("divide", Call("divide", Sub(I("lam"), b), g2), ck);
        var q = Sub(I("lam"), Mul(Mul(g2, ck), h));
        var psi = Sub(I("lam"), Mul(Mul(g2, ck),
            Call("divide", a, Sub(D(1), Mul(I("rho"), ck)))));
        var bound = Sub(h, Mul(Pow(I("rho"), rm), Sub(h, Mul(I("chi"), a))));
        Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
        Formula Output(Formula z) => Call("returnMap", high, reset, z);
        var z = I("z"); var m = I("m"); var r = I("r"); var state = I("D");
        var difference = Sub(Sub(h, Mul(Pow(I("rho"), Add(m, D(1))),
                Sub(h, Mul(Pow(I("chi"), r), z)))),
            Sub(h, Mul(Pow(I("rho"), m), Sub(h, Mul(Pow(I("chi"), r), h)))));
        var brace = Add(Sub(a, Mul(Pow(I("chi"), r), h)),
            Mul(Mul(I("rho"), Pow(I("chi"), r)), z));
        var source = I("sourceModel"); var target = I("targetModel");
        var cons = Call("cons", reset, xs);
        var conclusion = And(Equal(Call("r", reset), D(1)),
            Call("lt", Call("max", Call("max", Call("xSide", high), Call("ySide", high)), d), bound),
            All(Imp(Call("lt", a, state), Call("lt", bound, Output(state))), B("D", I("Real"))),
            All(Imp(Call("le", a, state), Call("le", bound, Output(state))), B("D", I("Real"))),
            All(Imp(Call("GuardTrace", k, d, I("false"), high, xs, Call("initial", high, source)),
                Call("ActualPairSupply", target, o, b, I("strict"), cons)),
                B("sourceModel", I("Model")), B("targetModel", I("Model")), B("xs", Returns)),
            All(Equal(Call("listWeight", cons), Add(Add(D(2, 0), Mul(D(6), rm)), Call("listWeight", xs))),
                B("xs", Returns)),
            All(Imp(And(Call("le", D(1), m), Call("le", D(1), r), Call("le", r, k), Call("le", a, z)),
                And(Equal(difference, Mul(Pow(I("rho"), m), brace)), Call("lt", D(0), difference))),
                B("m", I("Nat")), B("r", I("Nat")), B("z", I("Real"))));
        return Disp(All(Imp(And(Call("le", D(2), k), Call("lt", q, b), Call("lt", b, psi)),
            new Formula.BindMany(FormulaQuantifier.Exists, [B("R", I("Return"))], conclusion)),
            B("o", I("Ownership")), B("b", I("Real")), B("K", I("Nat"))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both actual Fibonacci starts retain the complete-boundary, closed and strict source laws and one finite actual reset map.",
        H("Actual boundaries for Fibonacci completion"),
        Blocks(
            Describe.Lean(DescribeId.Create("fib-actual-closed-record-supply"),
                DeclarationHandle.Create(Prefix + "actual_closed_record_supply"),
                H("Closed supply and owned high-guard equality"),
                StatementSource.FromAuthor(ClosedRecordSupply()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either fixed original or anchored source pair, closed acquisition is equivalent to the cap and high guard. Owning the first cut point permits equality; otherwise the high guard is strict. The proof assembles all departure errors on those same literal sources, through every six- and twenty-slot repetition, stem and paid anchor, and extends them by zero on the unchanged original futures. High equality uses the owned nearest point from the actual clipped readout law. The paired low costs are strictly smaller. All five flags remain parameters, and returns beyond the cap fail at the actual control slot."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-actual-reset-first-return"),
                DeclarationHandle.Create(Prefix + "actual_reset_first_return"),
                H("One paid actual reset and first-return output dominance"),
                StatementSource.FromAuthor(ResetFirstReturn()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A single positive finite reset length M gives B_M greater than X_H, Y_H and d. Its actual input above A gives output strictly above B_M; an input at least A gives the stated weak bound. Prepending this same reset to any weakly guarded complete list from either actual start supplies the complete paired record strictly from either target start, including the stems, anchor and original zero-error futures. The weight increases by exactly 20+6M. The exact first-run insertion identity gives strict output dominance after one added u for every original m,r,z in the stated domain. This extra u follows the first visible c-run even when it is low; no undiminished reset margin is assigned to a later return."))),
                DescribeRole.Theorem))));
}
