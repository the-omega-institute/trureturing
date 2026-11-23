using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuQuarticGraphDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuQuarticGraph.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");
    private static readonly Formula Real = Seq(Mathbb, Grp(F.Id("R")));
    private static readonly Formula Vertices = F.Id("V");
    private static readonly Formula Graph = F.Id("G");
    private static readonly Formula Weights = new Formula.TypeArrow(Vertices, Real);
    private static readonly Formula Simplex = Call("simplex", Vertices);
    private static readonly Formula Alpha = Call("indepNum", Graph);
    private static readonly Formula Penalty = F.Id("eta");
    private static readonly Formula Scale = F.Id("kappa");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact simplex minima for the reduced Wu graph quartic.",
        H("Optimization on the finite probability simplex"),
        Blocks(
            Paragraph(Text("Let G be a simple graph on a finite nonempty vertex type V. The probability simplex consists of nonnegative functions w on V that sum to one. The support is the finite set of vertices with positive mass. For a nonempty finite set s, uniform(s) has weight 1/card(s) on s and zero elsewhere. The notation real casts a natural number to a real, and image applies a function to a set. The objective is the sum of the linear penalties eta(i) w(i) and kappa times the sum of the squared masses and the products w(i) w(j) over ordered adjacent pairs. Thus each undirected edge contributes twice.")),
            Describe.Lean(DescribeId.Create("independent-support-minimum"),
                DeclarationHandle.Create(Owner + "independent_support_minimum"),
                H("Independent-support improvements and attainment"),
                StatementSource.FromAuthor(Disp(Weighted())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For adjacent vertices with positive mass, transfer a signed amount t from the second to the first. The simplex permits the whole interval from minus the first mass to the second mass. The two squares and both orientations of the edge sum to the square of the fixed combined mass. All remaining terms are affine in t, so an endpoint has cost at most the initial cost. That endpoint strictly reduces the positive support. Strong induction on its cardinality gives the first assertion. Compactness of the simplex and continuity of the objective yield a minimizer, to which the same improvement applies. This argument allows arbitrary real linear penalties and scales."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("unpenalized-minimum"),
                DeclarationHandle.Create(Owner + "unpenalized_minimum"),
                H("The sharp unpenalized minimum"),
                StatementSource.FromAuthor(Disp(Unpenalized())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("With zero penalties, the objective on independent support is kappa times the sum of squares. Cauchy–Schwarz bounds this sum below by the reciprocal of the support size, which is at most the independence number. Equal weights on a maximum independent set attain the bound. This is the Motzkin–Straus minimum in complementary-graph form."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("wu-unpenalized-minimum"),
                DeclarationHandle.Create(Owner + "wu_unpenalized_minimum"),
                H("The positive-temperature Wu coefficient and sharp graph minimum"),
                StatementSource.FromAuthor(Disp(Sharp())),
                AssessedProvenance.FromRepo(Wu),
                Blocks(
                    Paragraph(Text("Write B_p(beta) = sinh((1 − 1/p) beta/2) / sinh(beta/(2p)). Set kappa = B_p(beta)²/4 times the exponential Schur complement from WuCriticalQuartic. The factor converts the coherence-normalized Schur complement to squared Gibbs masses. Both factors are strictly positive for beta > 0 and 1 < p < r.")),
                    Paragraph(Text("Apply the sharp unpenalized bound at the Wu coefficient. Dividing kappa by the positive minimum recovers the independence number.")),
                    Paragraph(Text("The graph statements start from the reduced objective. The signed operator-model Taylor expansion and the limit that produces the finite penalties are separate analytic steps. The explicit coefficient statement concerns positive inverse temperature. The graph optimization theorem also applies to an independently supplied coefficient at zero inverse temperature."))),
                DescribeRole.Theorem))));

    private static Formula Weighted()
    {
        var w = F.Id("w");
        var u = F.Id("u");
        var improve = All("w", Weights, Imp(Mem(w, Simplex), Some("u", Weights,
            And(Mem(u, Simplex), And(Independent(u), And(Call("subset", Support(u), Support(w)),
                Le(Cost(Penalty, Scale, u), Cost(Penalty, Scale, w))))))));
        var attain = Some("u", Weights, And(Mem(u, Simplex), And(Independent(u),
            All("w", Weights, Imp(Mem(w, Simplex), Le(Cost(Penalty, Scale, u), Cost(Penalty, Scale, w)))))));
        return OnGraph(All("eta", Weights, All("kappa", Real, And(improve, attain))));
    }

    private static Formula Unpenalized()
    {
        var target = new Formula.Fraction(Scale, Call("real", Alpha));
        return OnGraph(All("kappa", Real, Imp(Lt(D(0), Scale),
            UniformAttainment(Scale, target, Least(Scale, target)))));
    }

    private static Formula Sharp()
    {
        var b = F.Id("beta");
        var p = F.Id("p");
        var r = F.Id("r");
        var m = F.Id("m");
        var k = Call("wuCoefficient", b, p, r);
        var target = new Formula.Fraction(k, Call("real", Alpha));
        var recovery = new Formula.Fraction(k, m);
        var characterize = All("m", Real, Logic(Least(k, m), FormulaLogicOperator.Iff,
            And(Eq(m, target), And(Lt(D(0), m), Eq(Call("real", Alpha), recovery)))));
        var conclusion = UniformAttainment(k, target, characterize);
        return OnGraph(All("beta", Real, All("p", Real, All("r", Real,
            Imp(And(Lt(D(0), b), And(Lt(D(1), p), Lt(p, r))), conclusion)))));
    }

    private static Formula Least(Formula scale, Formula value) =>
        Call("IsLeast", Call("image", Call("graphObjective", Graph, D(0), scale), Simplex), value);

    private static Formula UniformAttainment(Formula scale, Formula value, Formula minimum)
    {
        var s = F.Id("s");
        var weights = Call("uniform", s);
        return Some("s", Call("Finset", Vertices), And(Call("IsNIndepSet", Graph, Alpha, s),
            And(Mem(weights, Simplex), And(Eq(Cost(D(0), scale, weights), value), minimum))));
    }

    private static Formula OnGraph(Formula claim) =>
        All("V", Call("Type", F.Id("u")), Seq(
            OpenBracket, Call("Fintype", Vertices), CloseBracket, Sp,
            OpenBracket, Call("Nonempty", Vertices), CloseBracket, Comma, Sp,
            All("G", Call("SimpleGraph", Vertices), claim)));

    private static Formula Support(Formula w) => Call("support", w);
    private static Formula Independent(Formula w) => Call("IsIndepSet", Graph, Support(w));
    private static Formula Cost(Formula penalty, Formula scale, Formula w) =>
        Call("graphObjective", Graph, penalty, scale, w);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Seq(Open, a, Close), op, Seq(Open, b, Close));
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mem(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
}
