using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Density;

internal sealed class RationalBracketCollisionDensityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Density/RationalBracketCollisionDensity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/larssonmanabe2026additive");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite rational-modulus bracket expression has an existing rational collision density.",
        H("Rational collision densities of bracket expressions"),
        Blocks(
            Paragraph(Text("Section 1 of Larsson–Manabe defines a bracket expression using finitely "
                + "many integer coefficients and positive rational moduli. Section 7, Question 20(iii), "
                + "separately asks whether its collision density is always rational. The result here "
                + "answers that rationality question, including existence of the limit. The other "
                + "characterisation, closed-form and game questions are outside its scope.")),
            Node("bracket", "A finite rational floor sum", "bracket", BracketFormula(),
                "The index n is natural and includes zero. Fin t includes the empty family at t=0. "
                + "Coefficients may have either sign. Int.floor takes a rational argument and returns "
                + "an integer; the sum is over all i in Fin t.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("collision", "Distinct image values at a positive shift", "collision", CollisionFormula(),
                "Both existential witnesses range over the complete sequence. Their indices need "
                + "not agree or be unique. The predicate is on a nonnegative integer x, so filtering "
                + "a finite interval counts each image value only once, even when the sequence repeats.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The rationality subquestion", "claim", Disp(Iff(Named("claim"), ClaimBody())),
                "The source question asks: Is it always rational? The limit uses real division by N "
                + "and the inclusive interval from zero to N. The value at N=0 does not affect the "
                + "limit at infinity. The positivity premises apply to all rational moduli and to k; "
                + "there is no monotonicity, injectivity, coefficient-sign or positive-drift premise.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Existence and rationality", "result", Disp(ClaimBody()),
                "Clearing the finitely many denominators constructs a positive index period q "
                + "and an integer drift d. On each index residue the sequence is an affine ray. "
                + "For positive drift, image membership is periodic beyond a bound; for nonpositive "
                + "drift, the nonnegative image has an empty tail. Collision membership inherits "
                + "eventual periodicity. EventualCycleAverage.eventual_cycle_average gives the "
                + "average of the resulting finite indicator cycle. That average is rational. "
                + "Shifting the count to N+1 and multiplying by (N+1)/N gives exactly the displayed "
                + "normalization. This argument includes the empty expression and zero drift. "
                + "The proof is repository-derived; the paper supplies the question and definitions.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("larsson-manabe-2026-rational-bracket-collision-density"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string id, string title, string name, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role,
        openProblemResolutionClaim: resolution);

    private static Formula BracketFormula()
    {
        var i = F.Id("i"); var n = F.Id("n"); var t = F.Id("t");
        var term = Multiply(App(F.Id("c"), i),
            App(Q("Int", "floor"), Par(Multiply(Cast(n, Rats()), App(F.Id("alpha"), i)))));
        var sum = App(Q("Finset", "sum"),
            Cast(Q("Finset", "univ"), Call("Finset", Call("Fin", t))),
            Par(Lambda("i", Call("Fin", t), term)));
        return Disp(Parameters(All("n", Nats(), Equal(
            Call("bracket", F.Id("c"), F.Id("alpha"), n), sum))));
    }

    private static Formula CollisionFormula()
    {
        var c = F.Id("c"); var alpha = F.Id("alpha");
        var k = F.Id("k"); var x = F.Id("x");
        Formula Image(Formula value) => Exists("n", Nats(),
            Equal(Call("bracket", c, alpha, F.Id("n")), Cast(value, Ints())));
        return Disp(Parameters(All("k", Nats(), All("x", Nats(),
            Iff(Call("collision", c, alpha, k, x), And(Image(x), Image(Par(Add(x, k)))))))));
    }

    private static Formula ClaimBody()
    {
        var c = F.Id("c"); var alpha = F.Id("alpha");
        var k = F.Id("k"); var n = F.Id("N"); var a = F.Id("a");
        var filtered = App(Q("Finset", "filter"), Par(Call("collision", c, alpha, k)),
            Par(App(Q("Finset", "range"), Par(Add(n, D(1))))));
        var ratio = new Formula.Fraction(Cast(App(Q("Finset", "card"), Par(filtered)), Reals()),
            Cast(n, Reals()));
        var limit = App(Q("Filter", "Tendsto"), Par(Lambda("N", Nats(), ratio)),
            Q("Filter", "atTop"), Par(Call("nhds", Cast(a, Reals()))));
        return Parameters(Implies(All("i", Call("Fin", F.Id("t")),
            Less(D(0), App(alpha, F.Id("i")))), All("k", Nats(),
            Implies(Less(D(0), k), Exists("a", Rats(), limit)))));
    }

    private static Formula Parameters(Formula body) => All("t", Nats(),
        All("c", Arrow(Call("Fin", F.Id("t")), Ints()),
        All("alpha", Arrow(Call("Fin", F.Id("t")), Rats()), body)));
    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Ints() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Rats() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Q(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Cast(Formula value, Formula type) => Par(Seq(value, Colon, Sp, type));
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Lambda(string n, Formula type, Formula body) =>
        Seq(Named("fun"), Sp, Par(Seq(F.Id(n), Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula All(string n, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), type, body);
    private static Formula Exists(string n, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), type, body);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Multiply(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Iff, Par(b));
}
