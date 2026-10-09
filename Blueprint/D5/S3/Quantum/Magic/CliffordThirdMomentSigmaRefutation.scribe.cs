using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Magic;

internal sealed class CliffordThirdMomentSigmaRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Magic/CliffordThirdMomentSigmaRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/zhu2024thirdmoments");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "In dimension five, the stochastic Lagrangian subspaces are exactly the stochastic orthogonal graphs. The same normalized two-qudit state has total aggregate 140241723/24017978 and nonsymmetric aggregate -3866145/24017978, refuting both lower bounds in Zhu, Mao and Yi's Conjecture 2.",
        H("The stochastic Lagrangian and nonsymmetric aggregates"),
        Blocks(
            Node("sigma", "Stochastic Lagrangian subspaces", SigmaFormula(),
                "The collection contains every submodule satisfying the quadratic condition, dimension three and membership of the all-ones pair. No additional graph condition is imposed.",
                "sigmaSubspaces", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("sym", "Permutation graph subspaces", SymFormula(),
                "The symmetric collection consists of the graphs of the permutation matrices of S three, with the source orientation of output followed by input.",
                "symSubspaces", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("ns", "Nonsymmetric subspaces", NsFormula(),
                "Remove precisely the permutation graph subspaces from the stochastic Lagrangian collection.",
                "nsSubspaces", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("sigmasum", "The full aggregate", AggregateFormula("kappaSigma", "sigmaSubspaces"),
                "Sum the source trace expectation kappa over all members of the stochastic Lagrangian collection.",
                "kappaSigma", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("nssum", "The nonsymmetric aggregate", AggregateFormula("kappaNs", "nsSubspaces"),
                "Sum the same trace expectation over the nonsymmetric collection.",
                "kappaNs", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The two universal lower bounds", ClaimFormula(),
                "The disjunction asserts either the full aggregate lower bound six or the nonsymmetric aggregate lower bound zero, each for every normalized state, every number of qudits and every prime dimension other than two. The order is the complex order.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("classification", "All subspaces are graphs in dimension five",
                Eq(Call("sigmaSubspaces", D(5)), Call("isoSubspaces", D(5))),
                "A vector in ZMod 5 cubed with zero coordinate sum and zero sum of squares is zero. In a stochastic Lagrangian subspace this makes the second projection injective: apply the quadratic condition to a pair with second component zero and to its sum with the all-ones pair. Both domain and codomain have dimension three, so the projection is a linear equivalence. Its inverse gives a matrix whose graph is the subspace; the quadratic condition makes this matrix an isometry, and the all-ones pair makes it stochastic. Conversely, every stochastic orthogonal graph satisfies all three defining conditions.",
                "sigmaSubspaces_five", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Both lower bounds fail", new Formula.Not(F.Id("claim")),
                "Use the normalized two-qudit state psi in dimension five. The graph classification identifies the full aggregate with the isotropic aggregate 140241723/24017978. There are six distinct permutation graphs, each with expectation one, so their removal gives nonsymmetric aggregate -3866145/24017978. The first value is less than six and the second is negative. Thus both universally quantified lower bounds fail.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("zhu-2024-clifford-third-moment-sigma-lower-bounds"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("clifford-sigma-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Of(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) => new Formula.Logic(Parenthesized(a), op, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Forall, Sp, x, Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Arrow(Formula a, Formula b) => Seq(Parenthesized(a), Sp, To, Sp, b);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Field(Formula d) => Call("ZMod", d);
    private static Formula Config(Formula d, Formula n) => Arrow(Fin(n), Field(d));
    private static Formula Vectors(Formula d, Formula n) => Arrow(Config(d, n), Complex());
    private static Formula Square(Formula a) => new Formula.Power(a, D(2));
    private static Formula Sum(Formula x, Formula type, Formula body) =>
        Seq(F.Sum, Underscore, Grp(Seq(x, Sp, Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula Lambda(Formula x, Formula type, Formula body) =>
        Parenthesized(Seq(x, Sp, Colon, Sp, type, Sp, Mapsto, Sp, body));

    private static Formula Instance(string name, Formula argument) =>
        Seq(OpenBracket, Call(name, argument), CloseBracket, Sp);
    private static Formula Subspaces(Formula d) => Call("Submodule", Field(d),
        Parenthesized(Seq(Parenthesized(Config(d, D(3))), Sp, Times, Sp,
            Parenthesized(Config(d, D(3))))));
    private static Formula SigmaFormula()
    {
        Formula d = F.Id("d"), t = F.Id("T");
        Formula set = Seq(OpenBrace, Sp, t, Sp, Colon, Sp, Subspaces(d), Sp, Bar, Sp,
            Call("IsStochasticLagrangian", d, t), Sp, CloseBrace);
        return All(d, Nat(), Seq(Instance("NeZero", d),
            Eq(Call("sigmaSubspaces", d), Call("toFinset", set))));
    }
    private static Formula SymFormula()
    {
        Formula d = F.Id("d"), e = F.Id("e");
        Formula perms = Call("Perm", Fin(D(3)));
        return All(d, Nat(), Eq(Call("symSubspaces", d),
            Call("image", Lambda(e, perms, Call("graphSubspace", Call("permMatrix", e, Field(d)))),
                Call("univ", perms))));
    }
    private static Formula NsFormula()
    {
        Formula d = F.Id("d");
        return All(d, Nat(), Seq(Instance("NeZero", d), Eq(Call("nsSubspaces", d),
            Seq(Call("sigmaSubspaces", d), Sp, Setminus, Sp, Call("symSubspaces", d)))));
    }
    private static Formula AggregateFormula(string aggregate, string collection)
    {
        Formula d = F.Id("d"), n = F.Id("n"), psi = F.Id("Psi"), t = F.Id("T");
        Formula domain = Seq(t, Sp, Colon, Sp, Subspaces(d), Comma, Sp,
            t, Sp, InMacro, Sp, Call(collection, d));
        Formula sum = Seq(F.Sum, Underscore, Grp(domain), Sp,
            Parenthesized(Call("kappa", d, n, psi, t)));
        return All(d, Nat(), All(n, Nat(), Seq(Instance("NeZero", d),
            All(psi, Vectors(d, n), Eq(Call(aggregate, d, n, psi), sum)))));
    }
    private static Formula BoundFormula(string aggregate, Formula lower)
    {
        Formula d = F.Id("d"), n = F.Id("n"), psi = F.Id("Psi"), x = F.Id("x");
        Formula normalized = Eq(Sum(x, Config(d, n), Square(new Formula.Norm(Of(psi, x)))), D(1));
        return All(d, Nat(), Seq(Instance("Fact", Call("Prime", d)), Imp(Ne(d, D(2)),
            All(n, Nat(), All(psi, Vectors(d, n), Imp(normalized,
                Le(Parenthesized(Seq(lower, Sp, Colon, Sp, Complex())),
                    Call(aggregate, d, n, psi))))))));
    }
    private static Formula ClaimFormula() => Iff(F.Id("claim"),
        Logic(BoundFormula("kappaSigma", D(6)), FormulaLogicOperator.Or, BoundFormula("kappaNs", D(0))));
}
