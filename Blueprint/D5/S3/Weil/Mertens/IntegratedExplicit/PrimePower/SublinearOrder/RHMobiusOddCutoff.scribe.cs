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
                        + "The gap D(m,a,B) is a^(−s(m))−B^(−s(m)). The residual E(m,a,B) "
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
                        + "Its gap uses rate s(m)+δ(m). Integrate the exponential comparison over the "
                        + "closed logarithmic interval to bound the faster gap by "
                        + "((s(m)+δ(m))/s(m)) a^(−δ(m)) D(m,a,B). The inequality includes B=a."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signed-window-no-negative-order-exponent"),
                DeclarationHandle.Create(Owner + ".signed_window_no_negative_order_exponent"),
                H("A lower bound at arbitrarily late starts"),
                StatementSource.FromAuthor(Obstruction()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix positive γ, K and logarithmic width L. The function A "
                        + "can prescribe a lower endpoint threshold separately for each order. "
                        + "Euclid's theorem gives a prime q=m+1 beyond any required order. "
                        + "Its Möbius value is −1 and its leading coefficient exceeds 2.")),
                    Paragraph(Text("Choose the prime large enough that K m^(−γ)<1. "
                        + "After fixing the prime, choose a so late that the expansion error divided "
                        + "by D(m,a,B) is below 1. Positive L makes B=a exp(L)>a and the gap "
                        + "strictly positive. The signed residual then exceeds D(m,a,B)."))),
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
        var c = F.Id("C");
        var gap = Call("D", m, a, b);
        var correction = Multiply(Multiply(Call("mu", q),
            new Formula.Fraction(q, Multiply(m, Call("s", m)))), gap);
        var error = Le(new Formula.Absolute(Add(Call("E", m, a, b), correction)),
            Multiply(Multiply(c, new Formula.Power(a, new Formula.Negate(Call("delta", m)))), gap));
        var windows = All("a", Domain("R"),
            All("B", Domain("R"), Imp(And(Le(t, a), Le(a, b)), error)));
        var constants = Exists("T", Domain("R"), Exists("C", Domain("R"),
            And(And(Le(F.D(2), t), Lt(F.D(0), c)), windows)));
        return F.Disp(Imp(F.Id("RH"), All("m", Domain("N"),
            Imp(And(Le(F.D(2), m), Call("Odd", q)), constants))));
    }

    private static Formula Obstruction()
    {
        var m = F.Id("m");
        var n = F.Id("N");
        var a = F.Id("a");
        var k = F.Id("K");
        var gamma = F.Id("gamma");
        var l = F.Id("L");
        var b = Multiply(a, Call("exp", l));
        var gap = Call("D", m, a, b);
        var error = Lt(Multiply(Multiply(k, new Formula.Power(m, new Formula.Negate(gamma))), gap),
            new Formula.Absolute(Call("E", m, a, b)));
        var windows = Exists("m", Domain("N"), And(Le(Call("max", F.D(2), n), m),
            Exists("a", Domain("R"), And(Le(Call("max", F.D(2), Call("A", m)), a), error))));
        var ranges = All("A", F.Seq(Domain("N"), F.To, F.Sp, Domain("R")),
            All("N", Domain("N"), windows));
        var positive = And(And(Lt(F.D(0), gamma), Lt(F.D(0), k)), Lt(F.D(0), l));
        return F.Disp(Imp(F.Id("RH"), All("gamma", Domain("R"), All("K", Domain("R"),
            All("L", Domain("R"), Imp(positive, ranges))))));
    }
}
