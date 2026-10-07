using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class FacetRigidityBridgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rigidity of vanishing functionals on saturating generators gives affine codimension one.",
        H("From functional rigidity to a facet"),
        Blocks(Describe.Lean(DescribeId.Create("rigidity-facet-bridge"),
            DeclarationHandle.Create("D5/S3/QuantumBounds/FacetRigidityBridge.rigidity_facet_bridge"),
            H("The exposed face has affine codimension one"), StatementSource.FromAuthor(BridgeFormula()),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "Let s be any set in a finite-dimensional real module. The linear functional I is bounded below by b on s, and n normalises all its generators to one. The generator o attains the bound and t does not. If every linear functional vanishing on the saturating generators restricts to a scalar multiple of I−b on s, the exposed face of the convex hull has affine dimension one less than the hull. The notation vectorSpan is Mathlib's direction space of the affine span, so finrank here is affine dimension. A convex combination reaches the bound only through active saturating generators. The annihilator of the face direction space is the annihilator of the hull direction space plus the line through I; t shows that this line adds exactly one dimension."))),
            DescribeRole.Theorem))));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Parenthesized(a), op, Parenthesized(b));
    private static Formula Mem(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula LinearType(Formula e) => Call("LinearMap", Reals(), e, Reals());
    private static Formula Qualified(string owner, string name, params Formula[] args) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Call(name, args));
    private static Formula Instance(string name, Formula[] parameters, Formula body) =>
        Seq(OpenBracket, Call(name, parameters), CloseBracket, Sp, body);
    private static Formula And(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (int i = clauses.Length - 2; i >= 0; i--) result = Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula BridgeFormula()
    {
        Formula e = F.Id("E"), s = F.Id("s"), i = F.Id("I"), n = F.Id("n"), b = F.Id("b"),
            o = F.Id("o"), t = F.Id("t"), z = F.Id("z"), ell = F.Id("ell"), lam = F.Id("lam");
        Formula lower = All("z", e, Logic(Mem(z, s), FormulaLogicOperator.Implies, Le(b, Call("I", z))));
        Formula normalized = All("z", e, Logic(Mem(z, s), FormulaLogicOperator.Implies, Equal(Call("n", z), D(1))));
        Formula zero = All("z", e, Logic(Mem(z, s), FormulaLogicOperator.Implies,
            Logic(Equal(Call("I", z), b), FormulaLogicOperator.Implies, Equal(Call("ell", z), D(0)))));
        Formula rigidity = All("ell", LinearType(e), Logic(zero, FormulaLogicOperator.Implies,
            Some("lam", Reals(), All("z", e, Logic(Mem(z, s), FormulaLogicOperator.Implies,
                Equal(Call("ell", z), Multiply(lam, Parenthesized(Subtract(Call("I", z), b)))))))));
        Formula hull = Call("convexHull", Reals(), s);
        Formula face = Seq(OpenBrace, F.Id("p"), Colon, e, Mid,
            And(Mem(F.Id("p"), hull), Equal(Call("I", F.Id("p")), b)), CloseBrace);
        Formula dimension = Equal(Add(Qualified("Module", "finrank", Reals(),
            Call("vectorSpan", Reals(), face)), D(1)), Qualified("Module", "finrank", Reals(),
            Call("vectorSpan", Reals(), hull)));
        Formula body = Logic(And(lower, normalized, Mem(o, s), Equal(Call("I", o), b),
            Mem(t, s), NotEqual(Call("I", t), b), rigidity), FormulaLogicOperator.Implies, dimension);
        body = All("s", Call("Set", e), All("I", LinearType(e), All("n", LinearType(e),
            All("b", Reals(), All("o", e, All("t", e, body))))));
        body = Instance("FiniteDimensional", [Reals(), e], body);
        body = Instance("Module", [Reals(), e], body);
        body = Instance("AddCommGroup", [e], body);
        return Disp(All("E", F.Id("Type"), body));
    }
}
