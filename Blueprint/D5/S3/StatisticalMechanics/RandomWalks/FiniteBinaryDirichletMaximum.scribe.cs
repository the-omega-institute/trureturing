using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.RandomWalks;

internal sealed class FiniteBinaryDirichletMaximumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/RandomWalks/FiniteBinaryDirichletMaximum.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An attained absolute maximum propagates along every positive-weight transition to the zero boundary.",
        H("A maximum principle for two weighted successors"),
        Blocks(
            Node("maximum", "Zero boundary and exit paths force a zero maximum", "maximum_zero_of_two_successor_exit", MaximumFormula(),
                "A real-valued harmonic function has a uniform attained absolute maximum M. At every nonboundary state its two outgoing weights are nonnegative and sum to one. A successor with positive weight must have the same absolute value as a maximizing state. Propagating this equality along a finite positive-weight path to the zero boundary gives M = 0. The state type need not be finite: an attained uniform bound is sufficient.")), []));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("lee-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula QCall(string owner, string name, params Formula[] args) => App(Qualified(owner, name), args);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula All(string x, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), type, body);
    private static Formula Some(string x, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), type, body);
    private static Formula Arr(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Not(Formula a) => new Formula.Not(Parenthesized(a));
    private static Formula Lam(string x, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, F.Id(x), Colon, type, Sp, Mapsto, Sp, body);
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula MaximumFormula()
    {
        Formula S = F.Id("S"), f = F.Id("f"), M = F.Id("M"), boundary = F.Id("boundary");
        Formula l = F.Id("l"), r = F.Id("r"), a = F.Id("a"), b = F.Id("b"), s = F.Id("s"), t = F.Id("t");
        Formula sf = Arr(S, Real()), ss = Arr(S, S);
        Formula outside = Not(App(boundary, s));
        Formula step = Lam("s", S, Lam("t", S, And(outside,
            Or(And(Lt(D(0), App(a, s)), Eq(App(l, s), t)),
               And(Lt(D(0), App(b, s)), Eq(App(r, s), t))))));
        Formula bound = All("s", S, Le(new Formula.Absolute(App(f, s)), M));
        Formula attain = Some("s", S, Eq(new Formula.Absolute(App(f, s)), M));
        Formula zero = All("s", S, Imp(App(boundary, s), Eq(App(f, s), D(0))));
        Formula weights = All("s", S, Imp(outside, And(Le(D(0), App(a, s)),
            And(Le(D(0), App(b, s)), Eq(Add(App(a, s), App(b, s)), D(1))))));
        Formula harmonic = All("s", S, Imp(outside, Eq(App(f, s),
            Add(Mul(App(a, s), App(f, App(l, s))), Mul(App(b, s), App(f, App(r, s)))))));
        Formula exit = All("s", S, Some("t", S,
            And(App(boundary, t), QCall("Relation", "ReflTransGen", step, s, t))));
        Formula conclusion = Imp(bound, Imp(attain, Imp(zero, Imp(weights, Imp(harmonic, Imp(exit, Eq(M, D(0))))))));
        return Disp(All("S", Named("Type"), All("f", sf, All("M", Real(),
            All("boundary", Arr(S, Named("Prop")), All("l", ss, All("r", ss,
            All("a", sf, All("b", sf, conclusion)))))))));
    }

}
