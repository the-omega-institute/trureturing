using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.ErdosUlam;

internal sealed class SublatticeConstructionsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/ErdosUlam/SublatticeConstructions.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rank arithmetic progression supplies a diamond, and a Boolean interval extends "
            + "a monochromatic sublattice by every same-coloured prefix outside the interval.",
        H("Diamonds and Boolean interval extensions"),
        Blocks(
            Paragraph(Text("Write P(r) for the initial segment of size r in Fin n, and "
                + "R(n,g,t) for the number of ranks r between zero and n with g(r)=t. "
                + "The rank colouring assigns g(|A|) to A. Every family of initial segments is closed under union and intersection.")),
            Node("interval-lift", "intervalLift", "Translation into a Boolean interval", LiftFormula(),
                "For b+k≤n, translate every element of A by b and adjoin the initial segment "
                    + "P(b). The resulting set lies between P(b) and P(b+k), has size b+|A|, "
                    + "and the translation preserves both union and intersection.",
                DescribeRole.Definition),
            Node("diamond-sublattice", "diamond_sublattice", "An additional diamond member", DiamondFormula(),
                "Suppose a<b<c≤n, a+c=2b, and the three ranks have colour t. They are "
                    + "consecutive occurrences of t: every rank strictly between a and c "
                    + "with colour t equals b. Start with all t-coloured initial segments "
                    + "and add X=P(a) union (P(c) minus P(b)). This set has size b and "
                    + "differs from P(b). Its intersection with P(b) is P(a), while their "
                    + "union is P(c). All remaining selected prefixes lie below P(a) or "
                    + "above P(c), so the enlarged family is a monochromatic sublattice "
                    + "with R(n,g,t)+1 members.", DescribeRole.Theorem),
            Node("interval-sublattice", "interval_sublattice", "Extension by exterior prefixes", IntervalFormula(),
                "Let L be a nonempty sublattice of the k-dimensional Boolean lattice whose "
                    + "members all have colour t under A↦g(b+|A|). Suppose it has at least "
                    + "one more member than the number of t-coloured ranks in the interval "
                    + "from b to b+k. Translate L into that interval and adjoin all "
                    + "t-coloured prefixes with ranks less than b or greater than b+k. "
                    + "Each exterior prefix is comparable with every translated member, "
                    + "so lattice closure is preserved. Translation is injective, and "
                    + "the two families are disjoint by cardinality. Their combined size "
                    + "is at least R(n,g,t)+1.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, Formula formula,
        string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Nat() => F.Id("Nat");
    private static Formula Bool() => F.Id("Bool");
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Lt(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Add(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula And(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Imp(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Family(Formula n) => Call("Finset", Call("Finset", Call("Fin", n)));
    private static Formula Coloring() => new Formula.TypeArrow(Nat(), Bool());
    private static Formula Count(Formula n, Formula g, Formula t) => Seq(
        OpenBrace, F.Id("r"), Sp, InMacro, Sp, Call("range", Add(n, D(1))), Sp, Bar, Sp,
        Eq(Call("g", F.Id("r")), t), CloseBrace);
    private static Formula Conclusion(Formula n, Formula g, Formula t) => Ex("M", Family(n),
        And(Call("IsSublattice", F.Id("M")),
            And(Call("Monochromatic", Call("rankColouring", g), F.Id("M")),
                Le(Add(Call("card", Count(n, g, t)), D(1)), Call("card", F.Id("M"))))));

    private static Formula LiftFormula() => Disp(Seq(
        Call("intervalLift", F.Id("n"), F.Id("b"), F.Id("k"), F.Id("h"), F.Id("A")),
        Sp, F.Eq, Sp, Call("union", Call("P", F.Id("b")),
            Call("image", Call("translation", F.Id("b")), F.Id("A")))));

    private static Formula DiamondFormula()
    {
        var n = F.Id("n"); var a = F.Id("a"); var b = F.Id("b");
        var c = F.Id("c"); var g = F.Id("g"); var t = F.Id("t"); var r = F.Id("r");
        var gap = All("r", Nat(), Imp(And(Lt(a,r), And(Lt(r,c), Eq(Call("g",r),t))), Eq(r,b)));
        var conditions = And(Lt(a,b), And(Lt(b,c), And(Le(c,n),
            And(Eq(Add(a,c), Add(b,b)), And(Eq(Call("g",a),t),
                And(Eq(Call("g",b),t), And(Eq(Call("g",c),t), gap)))))));
        return Disp(All("n", Nat(), All("a", Nat(), All("b", Nat(), All("c", Nat(),
            All("g", Coloring(), All("t", Bool(), Imp(conditions, Conclusion(n,g,t)))))))));
    }

    private static Formula IntervalFormula()
    {
        var n = F.Id("n"); var b = F.Id("b"); var k = F.Id("k");
        var g = F.Id("g"); var t = F.Id("t"); var l = F.Id("L"); var a = F.Id("A");
        var monochromatic = All("A", Call("Finset", Call("Fin",k)),
            Imp(Call("member",a,l), Eq(Call("g",Add(b,Call("card",a))),t)));
        var window = Seq(OpenBrace, F.Id("r"), Sp, InMacro, Sp, Call("range",Add(k,D(1))),
            Sp, Bar, Sp, Eq(Call("g",Add(b,F.Id("r"))),t), CloseBrace);
        var conditions = And(Le(Add(b,k),n), And(Call("IsSublattice",l), And(monochromatic,
            Le(Add(Call("card",window),D(1)),Call("card",l)))));
        return Disp(All("n",Nat(),All("b",Nat(),All("k",Nat(),All("g",Coloring(),
            All("t",Bool(),All("L",Family(k),Imp(conditions,Conclusion(n,g,t)))))))));
    }
}
