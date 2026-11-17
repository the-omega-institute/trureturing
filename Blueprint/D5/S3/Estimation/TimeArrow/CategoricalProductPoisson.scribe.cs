using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.TimeArrow;

internal sealed class CategoricalProductPoissonDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Estimation/TimeArrow/CategoricalProductPoisson.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite categorical increments admit a uniform comparison with the full independent Poisson count vector.",
        H("Categorical increments and full product Poisson counts"), Blocks(
            Describe.Lean(DescribeId.Create("unit-mark"), DeclarationHandle.Create(Module + "unitMark"),
                H("One mark as a count vector"), StatementSource.FromAuthor(Disp(UnitFormula())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The vector has one at the selected mark and zero at every other mark."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("categorical-increment"), DeclarationHandle.Create(Module + "categoricalIncrement"),
                H("Categorical increment law"), StatementSource.FromAuthor(Disp(CategoricalFormula())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Rates are nonnegative real numbers, identified with their extended nonnegative real coercions when scaling measures. zeroVector(J) is the identically zero natural count vector. ofReal converts a real number to a nonnegative extended real, clipping negative values to zero. Under total rate rho at most one, this is a probability measure: the zero vector has probability one minus rho and the unit vector at j has probability a(j)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("aggregate-counts"), DeclarationHandle.Create(Module + "aggregateCounts"),
                H("Coordinatewise time aggregation"), StatementSource.FromAuthor(Disp(AggregationFormula())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Every coordinate is summed along the same complete history of s increments. An empty history produces the zero vector."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("independent-sum-law"), DeclarationHandle.Create(Module + "independentSumLaw"),
                H("Law of independent increments"), StatementSource.FromAuthor(Disp(SumLawFormula())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("finiteProduct denotes the measure product with one copy of mu for each element of Fin(s). pushforward maps that joint measure through aggregateCounts. Independence is part of the full increment law, rather than an assertion about separate marginals."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("categorical-product-poisson"), DeclarationHandle.Create(Module + "categorical_product_poisson"),
                H("Every-event product Poisson comparison"), StatementSource.FromAuthor(Disp(ComparisonFormula())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("eventMass is Measure.real applied to the event. poissonProduct is the measure product over all marks of the Poisson laws, and scaledRates(s,a)(j) is s times a(j). The theorem quantifies every finite alphabet, all nonnegative rates of total at most one, every natural s, and every event of the entire natural count vector. Empty alphabets, total rate zero, individual zero rates, and s equal to zero or one remain included.")),
                    Paragraph(Text("The proof constructs a common submeasure. It retains the categorical mass at zero and the full product Poisson mass exp(-rho) a(j) at each unit vector. Its mass is 1-rho(1-exp(-rho)). The s-fold increment product retains the corresponding power of this mass. Mapping the whole history to its count vector preserves domination. Bernoulli's inequality and exp(-rho) at least 1-rho give the displayed uniform bound. All events outside the unit vectors, including arbitrarily many Poisson arrivals, remain in the complement controlled by the common-submeasure argument.")),
                    Paragraph(Text("Time aggregation of the full product Poisson measure is proved through the finite product equivalence and Mathlib's poissonMeasure_conv_poissonMeasure, giving independent coordinates at rates s a(j). This is a finite categorical reference comparison. A comparison from the native path law to this reference is a separate mathematical obligation.")),
                    Paragraph(Text("For signed support marks J=Fin(q)+Fin(q), n=2M and a(j,+)=(1+r)/(2n), a(j,-)=(1-r)/(2n), the total rate is q/n and the final rates are L(1+r)/2 and L(1-r)/2, where L=s/n. The same joint count carrier is used for both signs; this application alone does not prove the native path comparison or close all clauses of the parent theorem.")),
                    Paragraph(Text("For the native application, assume 1 <= q < M, 0 < r < 1 and rq/(M-q) < 1. Fix S : Support(M,q) and an injective enumeration m : Fin(q) -> Fin(M) with every m(j) in S. On a native path observation o, define N(o)(inl(j)) = count(path,o,m(j),1) and N(o)(inr(j)) = count(path,o,m(j),-1). Its event probability is the sum of probability(r,path,S,o) over exactly the observations with N(o) in E. If a separate native comparison bounds its difference from independentSumLaw(categoricalIncrement(a),s)(E) by eta, the triangle inequality and this theorem give eta + s(q/n)^2 for its difference from the full product Poisson event probability. This implication preserves the fixed support and uses all counts on the same actual history; the native comparison premise remains a separate obligation."))), DescribeRole.Theorem))));

    private static Formula UnitFormula()
    {
        var value = Call("ite", Eqn(V("i"), V("j")), N(1), N(0));
        var equation = Eqn(Call("eval", Call("unitMark", V("j")), V("i")), value);
        return Q("J", Call("Type"), Inst("DecidableEq", Q("j", V("J"), Q("i", V("J"), equation))));
    }
    private static Formula CategoricalFormula()
    {
        var zero = Mul(Call("ofReal", Diff(N(1), SumRates())), Call("dirac", Call("zeroVector", V("J"))));
        var marks = SumF("j", V("J"), Mul(Call("eval", V("a"), V("j")), Call("dirac", Call("unitMark", V("j")))));
        var equation = Eqn(Call("categoricalIncrement", V("a")), Add(zero, marks));
        return Q("J", Call("Type"), Finite(Q("a", Arrow(V("J"), Call("NNReal")), equation)));
    }
    private static Formula AggregationFormula()
    {
        var sum = SumF("t", Call("Fin", V("s")), Call("eval", Call("eval", V("x"), V("t")), V("j")));
        var equation = Eqn(Call("eval", Call("aggregateCounts", V("s"), V("x")), V("j")), sum);
        return Q("J", Call("Type"), Q("s", Call("Nat"),
            Q("x", Arrow(Call("Fin", V("s")), Counts()), Q("j", V("J"), equation))));
    }
    private static Formula SumLawFormula()
    {
        var law = Call("pushforward", Call("aggregateCounts", V("s")), Call("finiteProduct", Call("Fin", V("s")), V("mu")));
        var equation = Eqn(Call("independentSumLaw", V("mu"), V("s")), law);
        return Q("J", Call("Type"), Q("mu", Call("Measure", Counts()), Q("s", Call("Nat"), equation)));
    }
    private static Formula ComparisonFormula()
    {
        var categorical = Call("eventMass", Call("independentSumLaw", Call("categoricalIncrement", V("a")), V("s")), V("E"));
        var poisson = Call("eventMass", Call("poissonProduct", Call("scaledRates", V("s"), V("a"))), V("E"));
        var bound = Le(Abs(Diff(categorical, poisson)), Mul(V("s"), Pow(SumRates(), N(2))));
        var events = Q("s", Call("Nat"), Q("E", Call("Set", Counts()), bound));
        var premise = Imp(Le(SumRates(), N(1)), events);
        return Q("J", Call("Type"), Finite(Q("a", Arrow(V("J"), Call("NNReal")), premise)));
    }

    private static Formula V(string s) => F.Id(s);
    private static Formula N(byte n) => D(n);
    private static Formula Call(string name, params Formula[] args)
    {
        var p = new List<Formula> { Operatorname, Grp(V(name)), Open };
        for (var i = 0; i < args.Length; i++) { if (i > 0) p.AddRange([Comma, Sp]); p.Add(args[i]); }
        p.Add(Close); return Seq([.. p]);
    }
    private static Formula Q(string x, Formula t, Formula b) => Seq(Forall, Sp, V(x), Colon, Sp, t, Comma, Sp, b);
    private static Formula Inst(string name, Formula b) => Seq(OpenBracket, Call(name, V("J")), CloseBracket, Sp, b);
    private static Formula Finite(Formula b) => Inst("Fintype", Inst("DecidableEq", b));
    private static Formula Arrow(Formula a, Formula b) => Seq(a, To, Sp, b);
    private static Formula Counts() => Arrow(V("J"), Call("Nat"));
    private static Formula Eqn(Formula a, Formula b) => Seq(a, F.Eq, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(a, Sp, Rightarrow, Sp, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Plus, b);
    private static Formula Diff(Formula a, Formula b) => Seq(a, Minus, b);
    private static Formula Mul(Formula a, Formula b) => Seq(Grp(a), Sp, Cdot, Sp, Grp(b));
    private static Formula Abs(Formula a) => Seq(Lvert, Sp, a, Sp, Rvert);
    private static Formula Pow(Formula a, Formula b) => Seq(Grp(a), Caret, Grp(b));
    private static Formula SumF(string x, Formula t, Formula b) => Seq(F.Sum, Underscore, Grp(V(x), Colon, Sp, t), Sp, Grp(b));
    private static Formula SumRates() => SumF("j", V("J"), Call("eval", V("a"), V("j")));
}
