using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.BoundedDegree;

internal sealed class ParkingConjecture52Document : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Graph/BoundedDegree/ParkingConjecture52.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/higuitadiazlopezroldancorrea2026parking");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fifteen-vertex tree of maximum degree three reverses the proposed lower-tail inequality at six parked vertices.",
        H("A subcubic counterexample to stochastic dominance in discrete parking"),
        Blocks(
            Definition("after", "Removing the chosen vertex and its neighbors", After(),
                "The available vertices after choosing v are the elements w of the current set with w distinct from v and no edge from v to w. The transition is on the original simple graph."),
            Definition("seq", "The sequential occupancy CDF", Sequential(),
                "With an empty available set the probability of at most k further choices is one for every natural cutoff k. A nonempty set at cutoff zero has probability zero. With a nonempty set at cutoff k+1, average the CDF at cutoff k over the available sets after each possible next choice. Expanding this recursion gives the product of inverse available-set sizes for each complete ordered history. The initial available set is the full vertex set."),
            Definition("jammed", "Jammed configurations", Jammed(),
                "A finite vertex subset is jammed when its underlying set is inclusion-maximal among independent sets of the graph."),
            Definition("static", "The static occupancy CDF", Static(),
                "Filter the power set of the full vertex set to the jammed sets. Divide the number of those sets with at most k vertices by the number of all jammed sets. The ratio is taken in the exact rationals."),
            Describe.Lean(DescribeId.Create("conjecture"), DeclarationHandle.Create(Module + "Conjecture52"),
                H("Conjecture 5.2"), StatementSource.FromAuthor(Disp(Claim())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Definition 2.1 compares the probabilities of occupancy at most k for every nonnegative integer k, represented here by a natural number. Conjecture 5.2 quantifies over every finite simple graph with maximum degree at most three."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("refutation"), DeclarationHandle.Create(Module + "not_conjecture52"),
                H("Refutation of Conjecture 5.2"), StatementSource.FromAuthor(Disp(new Formula.Not(Claim()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Use vertices 0 through 14 and edges (0,7), (1,8), (2,9), (3,10), (4,11), " +
                    "(0,12), (1,12), (5,12), (2,13), (3,13), (6,13), (4,14), (7,14) and (9,14). " +
                    "Maximal independent sets are counted by testing independence and coverage by closed neighborhoods. " +
                    "Exactly one of the 55 sets has size at most six. " +
                    "Conditioning on the first choice and evaluating the residual-set recurrence gives sequential CDF 64/3375. " +
                    "The static CDF is 1/55. The sequential CDF exceeds it by 29/37125."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("higuita-diaz-lopez-roldan-correa-2026-parking-conjecture-52"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Definition(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(name), DeclarationHandle.Create(Module + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner), Dot, F.Id(name)));

    private static Formula Apply(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LambdaOf(Formula variable, Formula body) =>
        Seq(Open, LambdaLower, Sp, variable, Sp, Mapsto, Sp, body, Close);

    private static Formula Filter(Formula predicate, Formula set) =>
        Apply(Qualified("Finset", "filter"), predicate, set);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(Open, value, Colon, Sp, type, Close);

    private static Formula RationalCard(Formula set) =>
        Typed(Apply(Qualified("Finset", "card"), set), Seq(Mathbb, Grp(F.Id("Q"))));

    private static Formula After()
    {
        var g = F.Id("G");
        var s = F.Id("s");
        var v = F.Id("v");
        var w = F.Id("w");
        var excluded = new Formula.Logic(Equal(v, w), FormulaLogicOperator.Or,
            Apply(Qualified("SimpleGraph", "Adj"), g, v, w));
        return Equal(Call("after", g, s, v), Filter(LambdaOf(w, new Formula.Not(excluded)), s));
    }

    private static Formula Sequential()
    {
        var g = F.Id("G");
        var k = F.Id("k");
        var s = F.Id("s");
        var v = F.Id("v");
        var sum = Seq(new Formula.Subscript(Sum, Seq(v, Sp, InMacro, Sp, s)), Sp,
            Call("seq", g, k, Call("after", g, s, v)));
        var nonempty = Seq(s, Sp, Neq, Sp, Emptyset);
        return new Formula.Aligned([
            Seq(Call("seq", g, k, Emptyset), Amp, Eq, Sp, D(1)),
            Seq(Call("seq", g, D(0), s), Amp, Eq, Sp, D(0), Quad, Open, nonempty, Close),
            Seq(Call("seq", g, Seq(k, Sp, Plus, Sp, D(1)), s), Amp, Eq, Sp,
                new Formula.Fraction(sum, RationalCard(s)), Quad, Open, nonempty, Close)
        ]);
    }

    private static Formula Jammed()
    {
        var g = F.Id("G");
        var s = F.Id("s");
        var independent = Apply(Qualified("SimpleGraph", "IsIndepSet"), g);
        return new Formula.Logic(Call("jammed", g, s), FormulaLogicOperator.Iff,
            Call("Maximal", independent, Typed(s, Call("Set", F.Id("V")))));
    }

    private static Formula Static()
    {
        var g = F.Id("G");
        var s = F.Id("s");
        var k = F.Id("k");
        var m = F.Id("m");
        var vertices = Typed(Qualified("Finset", "univ"), Call("Finset", F.Id("V")));
        var jammedSets = Filter(LambdaOf(s, Call("jammed", g, s)),
            Apply(Qualified("Finset", "powerset"), vertices));
        var atMost = Filter(LambdaOf(s, Le(Apply(Qualified("Finset", "card"), s), k)), m);
        return new Formula.Aligned([
            Seq(m, Amp, Eq, Sp, jammedSets),
            Seq(Call("static", g, k), Amp, Eq, Sp,
                new Formula.Fraction(RationalCard(atMost), RationalCard(m)))
        ]);
    }

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Instance(Formula type) => Seq(OpenBracket, type, CloseBracket, Sp);

    private static Formula Claim()
    {
        var v = F.Id("V");
        var g = F.Id("G");
        var k = F.Id("k");
        var comparison = All("k", F.Id("Nat"),
            Le(Call("seq", g, k, F.Id("univ")), Call("static", g, k)));
        var degree = new Formula.Logic(Le(Call("maxDegree", g), D(3)),
            FormulaLogicOperator.Implies, comparison);
        return All("V", F.Id("Type"), Seq(Instance(Call("Fintype", v)),
            Instance(Call("DecidableEq", v)), All("G", Call("SimpleGraph", v),
                Seq(Instance(Call("DecidableRel", Call("Adj", g))), degree))));
    }
}
