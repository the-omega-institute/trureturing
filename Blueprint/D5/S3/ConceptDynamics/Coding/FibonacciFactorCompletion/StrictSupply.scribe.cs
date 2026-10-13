using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion;

internal sealed class StrictSupplyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/StrictSupply.";
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

    private static Formula BoundaryGeometry()
    {
        var model = I("model"); var xs = I("execution"); var j = I("j");
        var p = I("p"); var n = I("n"); var k = I("k");
        Formula State(Formula side) => Call("execute", side, Call("take", xs, p),
            Call("initial", side, model));
        Formula Internal(Formula side) => Sub(Call("hSide", side),
            Mul(Pow(I("rho"), k), Sub(Call("hSide", side), Mul(Pow(I("chi"), n), State(side)))));
        var z = Internal(j);
        var signed = Add(I("c0"), Mul(Call("sign", j), z));
        return Disp(All(And(
            All(And(Call("lt", Call("aSide", j), State(j)), Call("lt", State(j), Call("hSide", j))),
                B("j", I("Side")), B("p", I("Nat"))),
            All(Call("lt", State(I("high")), State(I("low"))), B("p", I("Nat"))),
            All(And(Call("lt", D(0), z), Call("lt", z, Call("hSide", j)),
                Call("le", D(0), signed), Call("le", signed, I("T2"))),
                B("j", I("Side")), B("p", I("Nat")), B("n", I("Nat")), B("k", I("Nat"))),
            All(Call("lt", Internal(I("high")), Internal(I("low"))),
                B("p", I("Nat")), B("n", I("Nat")), B("k", I("Nat"))),
            All(Equal(Call("coordinate", Call("sourcePrefix", j, model, xs),
                    Add(Call("length", Call("stem", j)), Call("listWeight", Call("drop", xs, p)))),
                Add(I("c0"), Mul(Call("sign", j), State(j)))),
                B("j", I("Side")), B("p", I("Nat")))) ,
            B("model", I("Model")), B("execution", Returns)));
    }

    private static Formula StrictRecordSupply()
    {
        var model = I("model"); var o = I("o"); var b = I("b");
        var xs = I("execution"); var k = I("K"); var high = I("high");
        var h = Call("hSide", high); var a = Call("aSide", high);
        var ck = Pow(I("chi"), k); var g2 = Pow(I("g"), D(2));
        var z = Call("divide", a, Sub(D(1), Mul(I("rho"), ck)));
        var q = Sub(I("lam"), Mul(Mul(g2, ck), h));
        var psi = Sub(I("lam"), Mul(Mul(g2, ck), z));
        var d = Call("divide", Call("divide", Sub(I("lam"), b), g2), ck);
        var trace = Call("GuardTrace", k, d, I("true"), high, xs,
            Call("initial", high, model));
        Formula Supply(string contract) => Call("ActualPairSupply", model, o, b, I(contract), xs);
        Formula Iff(Formula x, Formula y) => And(
            new Formula.Logic(x, FormulaLogicOperator.Implies, y),
            new Formula.Logic(y, FormulaLogicOperator.Implies, x));
        return Disp(All(new Formula.Logic(
            And(Call("le", D(2), k), Call("lt", q, b), Call("lt", b, psi)),
            FormulaLogicOperator.Implies,
            And(Iff(Supply("strict"), trace), Iff(Supply("recordMargin"), trace))),
            B("model", I("Model")), B("o", I("Ownership")), B("b", I("Real")),
            B("execution", Returns), B("K", I("Nat"))));
    }

    private static Formula Imp(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula MarginEquivalence(Formula a, Formula b) => And(Imp(a, b), Imp(b, a));
    private static Formula AutomaticMarginG2 => Pow(I("g"), D(2));
    private static Formula AutomaticMarginHighState(Formula prefix) =>
        Call("execute", I("high"), prefix, Call("initial", I("high"), I("model")));
    private static Formula AutomaticMarginAnchorCost =>
        Sub(I("lam"), Mul(Mul(AutomaticMarginG2, I("chi")), Call("xSide", I("high"))));
    private static Formula AutomaticMarginStrictCostSupplier()
    {
        var stem = Sub(I("lam"), Mul(Mul(AutomaticMarginG2, I("chi")), AutomaticMarginHighState(I("execution"))));
        var costs = And(Call("lt", stem, I("budget")),
            Imp(Equal(I("model"), I("anchored")), Call("lt", AutomaticMarginAnchorCost, I("budget"))),
            Call("StrictControl", I("high"), I("budget"), I("execution"),
                Call("initial", I("high"), I("model"))));
        return Disp(All(Imp(Call("lt", Sub(I("lam"), I("rho")), I("budget")),
            MarginEquivalence(Call("ActualPairSupply", I("model"), I("o"), I("budget"),
                I("strict"), I("execution")), costs)),
            B("model", I("Model")), B("o", I("Ownership")), B("budget", I("Real")),
            B("execution", Returns)));
    }

    private static Formula Ex(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
    private static Formula SingletonReturn(Formula m, Formula r) =>
        Call("cons", Call("Return", m, r), Call("nil", I("Return")));
    private static Formula ActualDisplacementExtrema()
    {
        var j = I("j"); var xs = I("xs"); var d = I("D");
        var state = Call("execute", j, xs, Call("initial", j, I("original")));
        var values = Seq(OpenBrace, d, Sp, Colon, Sp, I("Real"), Sp, Mid, Sp,
            Ex(Equal(d, state), B("xs", Returns)), CloseBrace);
        return Disp(All(And(Equal(Call("sInf", values), Call("aSide", j)),
            Equal(Call("sSup", values), Call("hSide", j)),
            All(And(Call("lt", Call("aSide", j), state),
                Call("lt", state, Call("hSide", j))), B("xs", Returns))), B("j", I("Side"))));
    }
    private static Formula HighSingletonSlot()
    {
        var r = I("R");
        var z = Call("coordinate", Call("sourcePrefix", I("high"), I("original"),
            SingletonReturn(D(1), r)), D(3,0));
        var cost = Sub(I("lam"), Mul(Mul(Pow(I("g"), D(2)), Pow(I("chi"), r)),
            Call("xSide", I("high"))));
        return Disp(All(Imp(Call("lt", D(0), r), And(
            Equal(z, Sub(Call("cut", D(1)), cost)),
            Call("lt", z, Call("cut", D(1))),
            Equal(Call("max", Sub(Call("cut", D(1)), z),
                Call("max", D(0), Sub(z, Call("cut", D(2))))), cost))), B("R", I("Nat"))));
    }
    private static Formula HighHistory(Formula xs)
    {
        var p = I("p"); var err = I("err");
        var history = Call("history", I("original"), xs);
        return And(Call("ErrorBound", I("b"), I("contract"), err),
            All(Imp(Call("lt", p, Call("length", history)),
                Equal(Call("observe", I("o"),
                    Call("coordinate", Call("sourcePrefix", I("high"), I("original"), xs), p),
                    Call("apply", err, p)), Call("getElem", history, p))), B("p", I("Nat"))));
    }
    private static Formula HighFiniteCap()
    {
        var xs = I("xs"); var a = I("a");
        var bounded = All(Imp(And(Call("member", a, xs), HighHistory(xs)),
            Call("le", Call("r", a), I("K"))),
            B("o", I("Ownership")), B("contract", I("Contract")), B("xs", Returns),
            B("err", new Formula.TypeArrow(I("Nat"), I("Real"))), B("a", I("Return")));
        return Disp(All(Imp(Call("lt", I("b"), I("lam")), Ex(bounded, B("K", I("Nat")))),
            B("b", I("Real"))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both actual Fibonacci starts retain the complete-boundary, closed and strict source laws and one finite actual reset map.",
        H("Actual boundaries for Fibonacci completion"),
        Blocks(
            Describe.Lean(DescribeId.Create("fib-actual-complete-boundary-geometry"),
                DeclarationHandle.Create(Prefix + "actual_complete_boundary_geometry"), H("Actual complete boundaries and internal inputs"),
                StatementSource.FromAuthor(BoundaryGeometry()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every prefix of the common execution list, both actual initial states retain A_j < D_j < h_j and the high displacement is smaller than the low displacement. Internal inputs obtained by any number of C contractions and six-letter affine iterates remain positive and below h_j, keep the same side ordering, and their signed coordinates belong to [0,T2]. Each complete boundary is identified with the coordinate at stem length plus the weight of the unexecuted suffix in the same fixed source. The lower bound A_j is asserted only at complete boundaries, not at arbitrary internal cuts."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-actual-strict-record-supply"),
                DeclarationHandle.Create(Prefix + "actual_strict_record_supply"),
                H("Strict and per-record-margin supply on the original paired sources"),
                StatementSource.FromAuthor(StrictRecordSupply()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For K at least two and the original transition budget q_K < b < Psi_K, strict supply and per-record positive-margin supply of the independently defined actual source pair are each equivalent to the exact cap and strict high guard. The proof derives acquisition for arbitrary repetitions of the original six- and twenty-letter blocks, assembles all errors on the fixed same-list literal sources, and reads their original futures with zero error. It pays the stem and every repeated return, and the anchored template pays its own anchor using chi times X_H. Returns above the cap are rejected at the actual control cost; low returns are strictly supplied. Finite history errors give a positive margin for each record, without a common margin for an infinite family. All five endpoint flags remain arbitrary."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-actual-strict-cost-supply"),
                DeclarationHandle.Create(Prefix + "actual_strict_cost_supply"),
                H("Complete actual source costs above the nonactive-slot bound"),
                StatementSource.FromAuthor(AutomaticMarginStrictCostSupplier()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This supplier exposes the existing whole-source cost construction with its actual lower-budget hypothesis budget>lam-rho. It is the same fixed source, history, external block order and literal tail used by the strict record theorem. StrictControl recursively tests lam-g^2*chi^r*D at each actual return start. The stem tests chi times the final whole-list state, and the paid anchor tests chi times X_H, not its output Y_H.")),
                    Paragraph(Text("For a six-block input D<h_j, the nth outer input is h_j-rho^n*(h_j-D). Its active cost minus the next active cost is g^2*rho^n*(1-rho)*(h_j-D)>0. literal_full_slot_readout supplies every six-slot and twenty-slot departure above lam-rho. High/low ordering transports the high costs to the actual paired low source, and the finite departure errors extend by zero on the prescribed future."))),
                DescribeRole.Theorem),
            Paragraph(Text("Sharp endpoints of the original fixed-tail family")),
            Paragraph(Text("For j equal to high or low, A_j=(1-rho)h_j and X_j=A_j+rho*chi^3*E_j. The original initial displacement is X_j. The set below contains every finite positive Return list, including the empty list; it concerns complete right suffixes on the prescribed actual sources.")),
            Paragraph(Math(ActualDisplacementExtrema())),
            Paragraph(Text("The singleton lists [Return(1,R)] have displacement A_j+rho*chi^R*X_j, which tends to A_j as R tends to infinity. The lists [Return(M,1)] have displacement h_j-rho^M*(h_j-chi*X_j), which tends to h_j. The strict complete-boundary bounds exclude both endpoints for every finite list. X_j is not a valid lower bound: the original list [Return(1,3)] has displacement below X_j. Internal C inputs can be below A_j, while remaining positive.")),
            Paragraph(Text("Actual finite departure costs")),
            Paragraph(Text("For each side j, list xs and p less than length(history original xs), let z=coordinate(sourcePrefix j original xs,p) and i=history original xs[p]. Its closed-cell cost is max(cut(i)-z,max(0,z-cut(i+1))). actual_strict_cost_supply at budget lam supplies errors of absolute value strictly below lam at every such slot on the same source. literal_address_path supplies support, and owned_color_error, owned_color_interval and expanded_distance_formula imply that the cost is at most the absolute value of that actual error. Thus every finite departure cost is strictly below lam, including the stem and every repeated internal block. The terminal slot at history length is not included.")),
            Paragraph(Text("For the high singleton [Return(1,R)], R>0, departure 30 is the color-1 position in the U immediately next to C^R. Its complete right suffix is C^R followed by the prescribed high tail. The coordinate and closed distance are:")),
            Paragraph(Math(HighSingletonSlot())),
            Paragraph(Text("A bound from one prescribed high history")),
            Paragraph(Text("Suppose only that err satisfies ErrorBound b contract err and reads history original xs on the prescribed high source at every departure. No low history or future condition is needed. Write xs=before++[a]++after in execution order. External reversal places the selected return after externalWord high after, and its right complete suffix has displacement D=execute high before (initial high original). The active departure is q=26+length(externalWord high after)+6*(a.m-1)+4, in the last U next to C^(a.r), and its history color is 1. Its coordinate is cut(1)-(lam-g^2*chi^(a.r)*D). Closed-distance necessity gives lam-g^2*chi^(a.r)*D<=b. Since D<h_H, this forces g^2*chi^(a.r)*h_H>lam-b.")),
            Paragraph(Text("For each b<lam, geometric convergence permits an integer K with g^2*chi^r*h_H<lam-b whenever r>=K. Every return in any such high history then has r<K, and hence r<=K. This K depends only on b and the fixed system, uniformly over lists, m, ownership and all three error contracts. The empty list has no return to bound.")),
            Paragraph(Math(HighFiniteCap())),
            Paragraph(Text("This bound is necessary only. It supplies no subcritical sufficiency criterion, no rate transfer, and no assertion that restricted subfamilies have zero rate. Increasing m cannot remove the bound on r.")))));
}
