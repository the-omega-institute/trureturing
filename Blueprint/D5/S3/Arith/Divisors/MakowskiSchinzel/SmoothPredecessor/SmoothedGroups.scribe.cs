using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor;

internal sealed class SmoothPredecessorSmoothedGroupsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Grouped bound from arbitrary checked inputs", H("Grouped bound from arbitrary checked inputs"),
        Blocks(Describe.Lean(DescribeId.Create("smooth-predecessor-group-product"),
            DeclarationHandle.Create(
                "D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/SmoothedGroups." +
                "smooth_group_product"), H("The finite prefix and unbounded smooth tail"),
            StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For any encoded list E, tail constants t and final states z, assume " +
                "all entries pass validEntry, successor values have no repetitions, and the values " +
                "within each label group are nondecreasing. Assume also that " +
                "the recursive candidate count is at most length(E), t is the map of " +
                "tailData on oddPrimes, the run from initialState reaches z, and finalOk(t,z) " +
                "passes. Let Q have 98-smooth predecessors, successful candidate tests below bound, " +
                "and odd successors with non-power-of-two predecessors above bound. Then Q " +
                "satisfies the displayed grouped product bound. No primality of Q is assumed. " +
                "Validity, absence of repetitions and count give complete bounded coverage; " +
                "the tail map " +
                "identifies the constants in the run; the run and final test control all " +
                "group prefixes. Smoothness, oddness and the non-power-of-two condition give the large-predecessor " +
                "labels. Missing any of these inputs leaves the corresponding step unsupported. " +
                "The conclusion does not recover the supplied certificate: it holds for Q empty " +
                "even when a chosen input list fails its checks."))), DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var e = V("E"); var t = V("t"); var z = V("z"); var q = V("Q");
        var pred = Call("subOne", V("q"));
        var left = Seq(new Formula.Subscript(F.Prod,
            Seq(V("q"), Sp, InMacro, Sp, q)), Sp,
            new Formula.Fraction(V("q"), Call("subOne", V("q"))));
        var exponent = Seq(new Formula.Subscript(F.Sum,
            Seq(V("q"), Sp, InMacro, Sp, q)), Sp,
            Call("factorization", pred, V("p")));
        var right = Seq(new Formula.Subscript(F.Prod,
            Seq(V("p"), Sp, InMacro, Sp, Call("toFinset", V("oddPrimes")))), Sp,
            Call("geom", V("p"), exponent));
        var result = B(Then(Le(left, right),
            All("q", Nat(), Imp(Call("member", V("q"), q),
                Call("member", pred, Call("smoothNumbers", D(9,8))))),
            All("q", Nat(), Imp(Call("member", V("q"), q),
                new Formula.Logic(
                    Imp(Le(pred, V("bound")), Eq(Call("candidate", pred), True())),
                    FormulaLogicOperator.And,
                    Imp(new Formula.Relation(V("bound"), FormulaRelationOperator.LessThan, pred),
                        new Formula.Logic(Call("Odd", V("q")), FormulaLogicOperator.And,
                            Call("NotPowerOfTwo", pred))))))), ("Q", Call("Finset", Nat())));
        return B(Then(result,
            Eq(Call("all", V("validEntry"), e), True()),
            Call("Nodup", Call("map", V("entryValue"), e)),
            All("i", Nat(), Call("PairwiseLe", Call("groupValues", V("i"), e))),
            Le(Call("smoothSum", V("candidateWeight"), V("allPrimes"), V("bound"), D(2)),
                Call("length", e)),
            Eq(Call("map", V("tailData"), V("oddPrimes")), t),
            Eq(Call("stepTable", t, e, V("initialState")), Call("some", z)),
            Eq(Call("finalOk", t, z), True())),
            ("E", List(Nat())), ("t", List(Triple())), ("z", States()));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula List(Formula a) => Call("List", a);
    private static Formula Triple() => Call("Pair", Nat(), Call("Pair", Nat(), Nat()));
    private static Formula States() => List(Call("Pair", Nat(), Nat()));
    private static Formula True() => V("true");
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula B(Formula body, params (string Name, Formula Type)[] variables)
    {
        for (var i = variables.Length - 1; i >= 0; --i)
            body = All(variables[i].Name, variables[i].Type, body);
        return body;
    }
    private static Formula Then(Formula result, params Formula[] hypotheses)
    {
        for (var i = hypotheses.Length - 1; i >= 0; --i)
            result = Imp(hypotheses[i], result);
        return result;
    }
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
