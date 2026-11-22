using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class RHMobiusOddCutoffDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusOddCutoff";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The leading signed prime-window residual at odd cutoff",
        H("Compare neighboring truncation orders"),
        Blocks(
            Describe.Lean(DescribeId.Create("signed-window-odd-cutoff-expansion"),
                DeclarationHandle.Create(Owner + ".signed_window_odd_cutoff_expansion"),
                H("The first omitted arithmetic term"),
                StatementSource.FromAuthor(Expansion()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Write q=m+1, s(m)=1/2−1/q and δ(m)=1/q−1/(q+1). "
                        + "For any rate r the gap D(r,a,B) is a^(−r)−B^(−r). The residual E(m,a,B) "
                        + "subtracts the ordinary spectral endpoint difference and both signed corrections "
                        + "from the original window discrepancy.")),
                    Paragraph(Text("For 3≤n≤m the arithmetic correction has coefficient "
                        + "−2μ(n)n²/((n−1)(n−2)) and endpoint difference a^(1/n−1/2)−B^(1/n−1/2). "
                        + "For 2≤n≤m and 2n<m+1 the root correction is −μ(n) times the "
                        + "degree-n root primitive at B minus its value at a. Both spectral sums "
                        + "use actual nontrivial zeros counted with their analytic multiplicities.")),
                    Paragraph(Text("For odd q, the retained root degrees at orders m and q agree. "
                        + "The arithmetic sum gains only degree q. The all-order estimate at q "
                        + "therefore bounds the residual after the leading arithmetic term has been removed. "
                        + "The threshold T and multiplier K are common to all odd cutoffs. "
                        + "The weight W(K,m) is Kq(1+log q)². The sharper gap has rate s(m)+δ(m). "
                        + "Integrate the exponential comparison over the closed logarithmic interval "
                        + "to obtain the second inequality. Both include B=a."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signed-window-no-negative-order-exponent"),
                DeclarationHandle.Create(Owner + ".signed_window_no_negative_order_exponent"),
                H("A lower bound at arbitrarily late starts"),
                StatementSource.FromAuthor(Obstruction()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix positive γ and any real K. Choose one order threshold M "
                        + "such that K m^(−γ)<1 for all m≥M. At each prime q=m+1 in this range "
                        + "the Möbius value is −1 and the leading coefficient exceeds 2.")),
                    Paragraph(Text("For each such order, take the start threshold above A(m), 2 "
                        + "and the point where the normalized expansion error drops below 1. "
                        + "The gap is positive for every B>a. The signed residual exceeds the gap "
                        + "on all those windows. Unbounded primes give counterexamples to any "
                        + "uniform negative power, including at any prescribed positive logarithmic width."))),
                DescribeRole.Theorem))));

    private static Formula Domain(string name) => F.Seq(F.Mathbb, F.Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [..args]);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);

    private static Formula Expansion()
    {
        var m = F.Id("m");
        var q = Add(m, F.D(1));
        var a = F.Id("a");
        var b = F.Id("B");
        var t = F.Id("T");
        var k = F.Id("K");
        var rate = Call("s", m);
        var delta = Call("delta", m);
        var fasterRate = Add(rate, delta);
        var gap = Call("D", rate, a, b);
        var weight = Call("W", k, m);
        var fasterBound = Multiply(weight, Call("D", fasterRate, a, b));
        var correction = Multiply(Multiply(Call("mu", q),
            new Formula.Fraction(q, Multiply(m, rate))), gap);
        var productBound = Multiply(Multiply(Multiply(weight,
            new Formula.Fraction(fasterRate, rate)), new Formula.Power(a, new Formula.Negate(delta))), gap);
        var error = And(Le(new Formula.Absolute(Add(Call("E", m, a, b), correction)), fasterBound),
            Le(fasterBound, productBound));
        var windows = All("a", Domain("R"),
            All("B", Domain("R"), Imp(And(Le(t, a), Le(a, b)), error)));
        var orders = All("m", Domain("N"), Imp(And(Le(F.D(2), m), Call("Odd", q)), windows));
        return F.Disp(Imp(F.Id("RH"), Exists("T", Domain("R"), Exists("K", Domain("R"),
            And(And(Le(F.D(2), t), Lt(F.D(0), k)), orders)))));
    }

    private static Formula Obstruction()
    {
        var m = F.Id("m");
        var n = F.Id("N");
        var orderThreshold = F.Id("M");
        var startThreshold = F.Id("S");
        var a = F.Id("a");
        var b = F.Id("B");
        var k = F.Id("K");
        var gamma = F.Id("gamma");
        var gap = Call("D", Call("s", m), a, b);
        var error = Lt(Multiply(Multiply(k, new Formula.Power(m, new Formula.Negate(gamma))), gap),
            Call("E", m, a, b));
        var windows = All("a", Domain("R"), All("B", Domain("R"),
            Imp(And(Le(startThreshold, a), Lt(a, b)), error)));
        var starts = Exists("S", Domain("R"),
            And(Le(Call("max", F.D(2), Call("A", m)), startThreshold), windows));
        var orders = All("m", Domain("N"), Imp(And(Le(orderThreshold, m),
            Call("Prime", Add(m, F.D(1)))), starts));
        var ranges = All("A", F.Seq(Domain("N"), F.To, F.Sp, Domain("R")), All("N", Domain("N"),
            Exists("M", Domain("N"), And(Le(Call("max", F.D(2), n), orderThreshold), orders))));
        return F.Disp(Imp(F.Id("RH"), All("gamma", Domain("R"),
            Imp(Lt(F.D(0), gamma), All("K", Domain("R"), ranges)))));
    }
}
