using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive;

internal sealed class NathansonProblem15Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Additive/NathansonProblem15.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/nathanson2026hbases");
    private static readonly Formula N = Seq(Mathbb, Grp(F.Id("N")));
    private static readonly Formula Z = Seq(Mathbb, Grp(F.Id("Z")));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prescribed intervals and consecutive pairs in iterated integer sumsets",
        H("Nathanson's Problem 15"),
        Blocks(
            Node("digit", "digit", "Signed digit", DigitDefinition(),
                "The first label contributes one unit of its place and the second label contributes minus h − 1 units, multiplied by the respective counts.", DescribeRole.Definition),
            Node("radix-code", "radixCode", "Signed radix code", CodeDefinition(),
                "The base is h² + 1, one more than the width of the allowed digit interval.", DescribeRole.Definition),
            Node("radix-generators", "radixGenerators", "Radix generators", GeneratorDefinition(),
                "For each prescribed point, two generators are indexed by the two copies of Fin m.", DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nathanson-problem-fifteen"),
                DeclarationHandle.Create(Prefix + "nathanson_problem15"),
                H("The prescribed interval equivalences"),
                StatementSource.FromAuthor(Disp(Problem())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Section 5, Problem 15 asks for both interval equivalences and an estimate for the size of the finite generator set. "
                    + "The source indexes the starts from 1 through q. The Lean index i : Fin q represents source index i.val + 1. "
                    + "The natural parameters h, q and n have the stated lower bounds, N denotes the integer gap N_q, and x ranges over all integers in each equivalence. "
                    + "Pointwise scalar multiplication adds exactly h elements with repetitions allowed. "
                    + "The construction uses two labelled generators per prescribed point, giving at most 2q(n + 1) distinct generators. Each sum is represented by nonnegative label counts of total weight h, even when some generator values coincide. "
                    + "The signed digits are uᵢ − (h − 1)vᵢ. Their allowed interval has width h², so equal codes in base h² + 1 have equal digits by successively reducing modulo the base. "
                    + "If two distinct count pairs have equal digits, a change in a second-label count forces one pair to spend all h terms at a single index. Both pairs then have zero digits. A zero code uses h − 1 first labels and one second label at a single index, and its sum is exactly the prescribed point at that index. "
                    + "The construction scales the code by twice the remainder bound plus two, which separates unequal codes by at least two. "
                    + "Adjacent sums must share a code and come from distinct multiplicity pairs, so their common code is zero. Each is then a prescribed point, and the spacing forces both into one prescribed interval."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("nathanson-2026-problem-15-prescribed-intervals"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string name, string title, Formula statement, string prose,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("nathanson-fifteen-" + id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula IdOf(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(IdOf(name)));
    private static Formula Qualified(string owner, string name, params Formula[] args) =>
        App(Seq(Named(owner), Dot, Named(name)), args);
    private static Formula App(Formula head, params Formula[] args) => new Formula.Apply(head, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Named(name), args);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Binder(Formula quantifier, string name, Formula type, Formula body) =>
        Seq(quantifier, Sp, Par(Seq(IdOf(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula All(string name, Formula type, Formula body) => Binder(Forall, name, type, body);
    private static Formula Some(string name, Formula type, Formula body) => Binder(Exists, name, type, body);
    private static Formula Arrow(Formula source, Formula target) => new Formula.TypeArrow(source, target);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula AtMost(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula SubsetOf(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.SubsetOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula ImpliesTo(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, b);
    private static Formula Equivalent(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Iff, Par(b));
    private static Formula Cast(Formula a, Formula type) => Par(Seq(a, Sp, Colon, Sp, type));
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula Interval(Formula a, Formula b) => Qualified("Set", "Icc", a, b);
    private static Formula Sumset(Formula h, Formula a) => Qualified("SMul", "smul", h, a);
    private static Formula FinSum(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(IdOf(name), Sp, Colon, Sp, type)), Sp, Par(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(Named("fun"), Sp, Par(Seq(IdOf(name), Sp, Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula Cardinality(Formula a) => Qualified("Finset", "card", a);

    private static readonly Formula M = IdOf("m");
    private static readonly Formula Hh = IdOf("h");
    private static readonly Formula I = IdOf("i");
    private static readonly Formula J = IdOf("j");
    private static readonly Formula U = IdOf("u");
    private static readonly Formula V = IdOf("v");
    private static Formula FinM() => Fin(M);
    private static Formula Counts() => Arrow(FinM(), N);
    private static Formula Values() => Arrow(FinM(), Z);
    private static Formula Code(Formula u, Formula v) => Call("radixCode", Hh, u, v);

    private static Formula DigitDefinition() => All("m", N, All("h", N, All("u", Counts(), All("v", Counts(),
        All("i", FinM(), Equal(Call("digit", Hh, U, V, I),
            Sub(Cast(App(U, I), Z), Mul(Par(Sub(Cast(Hh, Z), D(1))), Cast(App(V, I), Z)))))))));


    private static Formula Base() => Par(Add(Pow(Cast(Hh, Z), D(2)), D(1)));

    private static Formula CodeDefinition() => All("m", N, All("h", N, All("u", Counts(), All("v", Counts(),
        Equal(Code(U, V), FinSum("i", FinM(), Mul(Call("digit", Hh, U, V, I),
            Pow(Base(), Qualified("Fin", "val", I)))))))));


    private static Formula GeneratorDefinition()
    {
        var scale = IdOf("M");
        var t = IdOf("t");
        var a = IdOf("a");
        var place = Mul(scale, Pow(Base(), Qualified("Fin", "val", I)));
        var second = LambdaOf("i", FinM(), Sub(App(t, I), Mul(Par(Sub(Cast(Hh, Z), D(1))), App(a, I))));
        var body = Seq(Named("let"), Sp, a, Sp, Colon, Sp, Par(Values()), Sp, Colon, Eq, Sp,
            LambdaOf("i", FinM(), place), Sp, Named("in"), Sp, Qualified("Sum", "elim", a, Par(second)));
        return All("m", N, All("h", N, All("M", Z, All("t", Values(),
            Equal(Call("radixGenerators", Hh, scale, t), Par(body))))));
    }


    private static Formula Problem()
    {
        var q = IdOf("q");
        var n = IdOf("n");
        var gap = IdOf("N");
        var c = IdOf("c");
        var x = IdOf("x");
        var a = IdOf("A");
        var start = App(c, I);
        var starts = Fin(q);
        var length = Cast(n, Z);
        var prescribed = Interval(start, Add(start, length));
        var adjacent = Interval(x, Add(x, D(1)));
        var hA = Sumset(Hh, Cast(a, Call("Set", Z)));
        var consecutive = Equal(Qualified("Fin", "val", J), Add(Qualified("Fin", "val", I), D(1)));
        var gaps = All("i", starts, All("j", starts,
            ImpliesTo(consecutive, AtMost(gap, Sub(App(c, J), start)))));
        var exactStarts = All("x", Z, Par(Equivalent(SubsetOf(Interval(x, Add(x, length)), hA),
            Some("i", starts, Equal(x, start)))));
        var exactPairs = All("x", Z, Par(Equivalent(SubsetOf(adjacent, hA),
            Some("i", starts, And(SubsetOf(adjacent, prescribed), SubsetOf(prescribed, hA))))));
        var size = AtMost(Cardinality(a), Mul(Mul(D(2), q), Par(Add(n, D(1)))));
        var conclusion = Some("A", Call("Finset", Z), And(size, And(exactStarts, exactPairs)));
        return All("h", N, All("q", N, All("n", N, All("N", Z,
            ImpliesTo(AtMost(D(2), Hh), ImpliesTo(AtMost(D(2), q), ImpliesTo(AtMost(D(1), n),
                ImpliesTo(AtMost(Add(length, D(2)), gap),
                    All("c", Arrow(starts, Z), ImpliesTo(gaps, conclusion))))))))));
    }
}
