using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.CellularAutomata;

internal sealed class HoneycombBirthKernelDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/StatisticalMechanics/CellularAutomata/HoneycombBirthKernel";
    private static readonly Formula Naturals = Seq(Mathbb, Grp(F.Id("N")));
    private static readonly Formula Integers = Seq(Mathbb, Grp(F.Id("Z")));
    private static readonly Formula Polynomial = Seq(Integers, OpenBracket, F.Id("X"), CloseBracket);
    private static readonly Formula Vertex = Name("Vertex");
    private static readonly Formula Vertices = CallNamed("Finset", Vertex);
    private static readonly Formula Graph = F.Id("G");
    private static readonly Formula Origin = CallNamed("A", Num(0), Num(0));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adjacent-cut birth polynomials and their normalized honeycomb kernels.",
        H("Birth polynomials of adjacent honeycomb cuts"),
        Blocks(
            Paragraph(Text("Here Vertex is Bool × ℤ × ℤ, x(v) and y(v) are its integer "
                + "coordinate projections, and e is Lean's typeclass argument for "
                + "decidable adjacency. Subtraction in tick and exponent expressions "
                + "is truncated in ℕ. The symbol X denotes the polynomial indeterminate.")),
            Definition("delta", "delta", "Adjacent-cut birth difference", DeltaDefinition(),
                "Each birth polynomial counts every retained vertex that is born with a monomial at its birth tick."),
            Definition("birth-weight", "birthWeight", "Birth indicator", BirthWeight(),
                "The value is an integer, so the difference of two such weights can be negative."),
            Definition("signed-weight", "signedWeight", "Difference of birth indicators", SignedWeight(),
                "The orientation is the weight at cut d minus the weight at cut d+1."),
            Theorem("coeff-delta-on", "coeff_delta_on", "Coefficient over a common finite set", CoeffDeltaOn(),
                "U contains the larger cut domain. Vertices outside each cut contribute zero to its birth count."),
            Paragraph(Text("At a positive multiple a of a dyadic strip width P, horizontal "
                + "translation identifies the right strip with the height-P run after "
                + "a delay of 2(a−P). On the left, the birth indicators for the two cuts agree.")),
            Theorem("adjacent-copy-of-earliest", "adjacent_copy_of_earliest",
                "Dyadic copy of the adjacent-cut difference", AdjacentCopy(),
                "The graph satisfies both the adjacency laws and the earliest-birth parity law. The same column c is used at both heights."),
            Paragraph(Text("At neighboring cuts of an integral height, write τ=2a−d−1 "
                + "for the removed layer's time. The potential 2τ−g+y changes by at "
                + "most one along an edge before conversion to a natural. On the removed "
                + "layer it equals the earliest possible touch time.")),
            Theorem("signed-support-of-neighbor-laws", "signedSupport_of_neighborLaws",
                "Support of the signed birth indicator", SignedSupport(),
                "The conclusion expands the private predicate SignedSupport. The layer time and "
                + "the natural index i are cast to integers before taking their difference."),
            Definition("kernel-entry", "kernelEntry", "Normalized kernel coefficient", KernelEntry(),
                "Choose the least natural exponent b with d < 2^b, then read the coefficient after the removed layer’s delay."),
            Theorem("kernel-entry-eq-coeff", "kernelEntry_eq_coeff",
                "Coefficient at any eligible dyadic height", KernelEntryEqCoeff(),
                "Any eligible dyadic height may be used with the same graph and parity law."),
            Definition("birth-kernel-entry", "birthKernelEntry", "Kernel coefficient on the repository graph",
                BirthKernelEntry(),
                "The specialized readout uses the existing honeycomb graph and its concrete adjacency decision procedure."))));

    private static DocumentBlock Definition(string id, string name, string title, Formula statement, string description) =>
        Mirror(id, name, title, statement, description, DescribeRole.Definition);

    private static DocumentBlock Theorem(string id, string name, string title, Formula statement, string description) =>
        Mirror(id, name, title, statement, description, DescribeRole.Theorem);

    private static DocumentBlock Mirror(string id, string name, string title, Formula statement,
        string description, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(description))), role);

    private static Formula DeltaDefinition()
    {
        var a = F.Id("a");
        var d = F.Id("d");
        return OnGraph(All(TypedEquation(CutDifference(a, d), Polynomial,
            Subtract(BirthPolynomial(a, d), BirthPolynomial(a, Add(d, Num(1))))),
            ("a", Naturals), ("d", Naturals)));
    }

    private static Formula BirthPolynomial(Formula a, Formula d)
    {
        var v = F.Id("v");
        var t = F.Id("t");
        var domain = OmegaDomain(a, d);
        var born = CallNamed("Born", Graph, domain, Origin, t, v);
        var first = Seq(Name("min"), Underscore, Grp(t, Sp, InMacro, Sp, Naturals, Sp, Mid, Sp, born));
        var eventExists = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("t"), Naturals, born);
        var monomial = CallNamed("ite", Par(eventExists), new Formula.Power(F.Id("X"), first), Num(0));
        return SumOver("v", domain, monomial);
    }

    private static Formula BirthWeight()
    {
        var domain = F.Id("D");
        var t = F.Id("t");
        var v = F.Id("v");
        var state = CallNamed("state", Graph, domain, Origin, t, v);
        var birth = Equal(state, CallNamed("some", Par(Seq(t, Comma, Sp, Num(1)))));
        return OnGraph(All(TypedEquation(Weight(domain, t, v), Integers,
            CallNamed("ite", birth, Num(1), Num(0))), ("D", Vertices), ("t", Naturals), ("v", Vertex)));
    }

    private static Formula SignedWeight()
    {
        var a = F.Id("a");
        var d = F.Id("d");
        var t = F.Id("t");
        var v = F.Id("v");
        return OnGraph(All(TypedEquation(SignedAt(a, d, t, v), Integers,
            Subtract(Weight(OmegaDomain(a, d), t, v), Weight(OmegaDomain(a, Add(d, Num(1))), t, v))),
            ("a", Naturals), ("d", Naturals), ("t", Naturals), ("v", Vertex)));
    }

    private static Formula CoeffDeltaOn()
    {
        var set = F.Id("U");
        var a = F.Id("a");
        var d = F.Id("d");
        var t = F.Id("t");
        var subset = new Formula.Relation(OmegaDomain(a, d), FormulaRelationOperator.SubsetOf, set);
        return OnGraph(All(Imp(subset, All(Equal(Coefficient(CutDifference(a, d), t),
            SumOver("v", set, SignedAt(a, d, t, F.Id("v")))), ("t", Naturals))),
            ("U", Vertices), ("a", Naturals), ("d", Naturals)));
    }

    private static Formula AdjacentCopy()
    {
        var a = F.Id("a");
        var c = F.Id("c");
        var p = Pow2(F.Id("b"));
        var divides = new Formula.Relation(p, FormulaRelationOperator.Divides, a);
        var delay = Multiply(Num(2), Par(Subtract(a, p)));
        var shifted = Multiply(new Formula.Power(F.Id("X"), delay), CutDifference(p, c));
        var equation = Imp(Less(Num(0), a), divides, LeqOf(Add(c, Num(1)), p),
            Equal(CutDifference(a, c), shifted));
        return OnGraph(Imp(Laws(), Par(Imp(Parity(), All(equation,
            ("b", Naturals), ("a", Naturals), ("c", Naturals))))));
    }

    private static Formula SignedSupport()
    {
        var a = F.Id("a");
        var d = F.Id("d");
        var j = F.Id("j");
        var v = F.Id("v");
        var i = F.Id("i");
        var time = LayerTime(a, d);
        var y = CallNamed("y", v);
        var layer = Equal(CallNamed("g", v), Subtract(CastInt(time), CastInt(i)));
        var bound = LeqOf(Add(i, App(Seq(Operatorname, Grp(F.Id("Int"), Dot, F.Id("toNat"))), y)), j);
        var index = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("i"), Naturals,
            And(layer, bound));
        var supported = And(new Formula.Relation(v, FormulaRelationOperator.MemberOf, OmegaDomain(a, d)), index);
        var nonzero = NotEqual(SignedAt(a, d, Add(time, j), v), Num(0));
        return OnGraph(Imp(Laws(), All(Imp(Less(d, a), All(Imp(nonzero, supported),
            ("j", Naturals), ("v", Vertex))), ("a", Naturals), ("d", Naturals))));
    }

    private static Formula KernelEntry()
    {
        var d = F.Id("d");
        var j = F.Id("j");
        var b = F.Id("b");
        var exponent = Seq(Name("min"), Underscore, Grp(b, Sp, InMacro, Sp, Naturals, Sp, Mid, Sp, Less(d, Pow2(b))));
        var enclosure = Pow2(exponent);
        return OnGraph(All(TypedEquation(Entry(Graph, j, d), Integers,
            Coefficient(CutDifference(enclosure, d), Add(LayerTime(enclosure, d), j))),
            ("j", Naturals), ("d", Naturals)));
    }

    private static Formula KernelEntryEqCoeff()
    {
        var d = F.Id("d");
        var j = F.Id("j");
        var p = Pow2(F.Id("b"));
        var equation = Equal(Entry(Graph, j, d), Coefficient(CutDifference(p, d), Add(LayerTime(p, d), j)));
        return OnGraph(Imp(Laws(), Par(Imp(Parity(), All(Imp(Less(d, p), equation),
            ("b", Naturals), ("d", Naturals), ("j", Naturals))))));
    }

    private static Formula BirthKernelEntry()
    {
        var j = F.Id("j");
        var d = F.Id("d");
        var specialization = CallNamed("kernelEntry", Name("honeycombGraph"), Name("repositoryAdjacency"), j, d);
        return All(TypedEquation(CallNamed("birthKernelEntry", j, d), Integers, specialization),
            ("j", Naturals), ("d", Naturals));
    }

    private static Formula OnGraph(Formula body) =>
        All(body, ("G", CallNamed("SimpleGraph", Vertex)),
            ("e", CallNamed("DecidableRel", Seq(Graph, Dot, Name("Adj")))));

    private static Formula Laws() => CallNamed("NeighborLaws", Graph);
    private static Formula Parity() => CallNamed("EarliestBirthIff", Graph);
    private static Formula CutDifference(Formula a, Formula d) => CallNamed("delta", Graph, a, d);
    private static Formula Weight(Formula domain, Formula t, Formula v) => CallNamed("birthWeight", Graph, domain, t, v);
    private static Formula SignedAt(Formula a, Formula d, Formula t, Formula v) => CallNamed("signedWeight", Graph, a, d, t, v);
    private static Formula Coefficient(Formula polynomial, Formula t) => CallNamed("coeff", polynomial, t);
    private static Formula OmegaDomain(Formula a, Formula d) => CallNamed("omegaDomain", a, d);
    private static Formula Entry(Formula graph, Formula j, Formula d) => CallNamed("kernelEntry", graph, j, d);
    private static Formula LayerTime(Formula a, Formula d) => Subtract(Subtract(Multiply(Num(2), a), d), Num(1));
    private static Formula Pow2(Formula b) => new Formula.Power(Num(2), b);
    private static Formula CastInt(Formula value) => Par(Seq(value, Colon, Sp, Integers));

    private static Formula Name(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula CallNamed(string name, params Formula[] arguments) => App(Name(name), arguments);
    private static Formula App(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula TypedEquation(Formula value, Formula type, Formula right) =>
        Equal(Par(Seq(value, Colon, Sp, type)), right);
    private static Formula SumOver(string variable, Formula domain, Formula summand) =>
        Seq(Sum, Underscore, Grp(F.Id(variable), Sp, InMacro, Sp, domain), Sp, Par(summand));
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LeqOf(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Par(left), FormulaLogicOperator.And, Par(right));
    private static Formula Imp(Formula premise, Formula body) =>
        new Formula.Logic(Par(premise), FormulaLogicOperator.Implies, Par(body));
    private static Formula Imp(Formula first, Formula second, Formula third, Formula body) =>
        Imp(first, Imp(second, Imp(third, body)));

    private static Formula All(Formula body, params (string Name, Formula Type)[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. variables.Select(variable => new Formula.BoundVariable(
                FormulaIdentifier.Create(variable.Name), variable.Type))], body);
}
