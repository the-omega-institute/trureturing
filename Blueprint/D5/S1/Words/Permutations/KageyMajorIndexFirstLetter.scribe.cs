using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Permutations;

internal sealed class KageyMajorIndexFirstLetterDocument : IScribeDocumentDefinition
{
    private const string Root = "D5/S1/Words/Permutations/KageyMajorIndexFirstLetter.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/kagey2021majorindex");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Major-index first-letter expectations have the monic rational form of Conjecture 5.2.",
        H("First letters at a fixed major index"),
        Blocks(
            Paragraph(Text("Permutations are Equiv.Perm (Fin n). Position i has one-based letter (pi i).val+1. "
                + "The adjacent-descent indicator is D5.S1.Words.Patterns.Separable.CutFactorization.descentAt. "
                + "All casts displayed with codomain Q are natural-number casts into the rational field.")),
            Node("maj", "The major index", MajorBody(),
                "Section 5.2, page 19: “Below, we have given conjectures about two: the major index and the inversion number.” "
                    + "The major index is the sum of one-based positions at which an adjacent descent occurs. "
                    + "The final position has descent indicator zero.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("count", "The conditioning cardinality", CountBody(),
                "Section 5.2, page 20: “Because the expected value of the first letter is given by the weighted sum of the permutations with mah(w) = k divided by the number of such permutations, E[π(1) | π ∈ S_n, mah(π) = k] has a denominator that is (a factor of) M(n, k), the number of permutations of w ∈ S_n such that inv(w) = k.” "
                    + "Here the statistic is maj. Each permutation occurs once in the finite set, which retains exactly major index k.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("E", "The conditional expectation", ExpectationBody(),
                "Section 5.2, page 20: “Because the expected value of the first letter is given by the weighted sum of the permutations with mah(w) = k divided by the number of such permutations, E[π(1) | π ∈ S_n, mah(π) = k] has a denominator that is (a factor of) M(n, k), the number of permutations of w ∈ S_n such that inv(w) = k.” "
                    + "Here the statistic is maj. Division takes place in Q; the theorem restricts to nonempty conditioning sets.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 5.2", Equal(V("claim"), Parenthesized(ClaimBody())),
                "Conjecture 5.2, page 20: “For fixed k > 0 and n ≥ k, E[π(1) | π ∈ S_n, maj(π) = k] satisfies a rational function in n that is 1/(k + 1) times the quotient of a monic degree-(k + 1) polynomial by a monic degree-k polynomial.” "
                    + "The nonzero cardinality hypothesis expresses that the conditional expectation is defined. "
                    + "The quotient need not be reduced, and n=k is included whenever the conditioning set is nonempty.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The monic rational form", ClaimBody(),
                "Increasing blocks give the cardinality and first-letter weighted sum as polynomials in n. "
                    + "Exact-descent inclusion–exclusion selects major index k. Only S=U={k} contributes "
                    + "to the highest coefficients, which are 1/k! and 1/(k+1)!. Scaling by these factorials "
                    + "gives monic Q and P of the required degrees. The source's n=k endpoint is retained.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("kagey-major-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Root + name), H(title), StatementSource.FromAuthor(Disp(formula)),
        provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula Naturals => Seq(Mathbb, Grp(V("N")));
    private static Formula Rationals => Seq(Mathbb, Grp(V("Q")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Q(params string[] names)
    {
        var items = new Formula[names.Length * 2 - 1];
        for (var i = 0; i < names.Length; i++)
        {
            items[i * 2] = V(names[i]);
            if (i + 1 < names.Length) items[i * 2 + 1] = Dot;
        }
        return Seq(Operatorname, Grp(items));
    }
    private static Formula App(Formula name, params Formula[] args) => new Formula.Apply(name, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Q(name), args);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Cast(Formula x) => Parenthesized(Seq(App(Q("Nat", "cast"), x), Colon, Sp, Rationals));
    private static Formula Val(Formula x) => Call("val", x);
    private static Formula Permutations => App(Q("Equiv", "Perm"), Call("Fin", V("n")));
    private static Formula FirstLetterValue(Formula pi)
    {
        var positive = Seq(Q("if"), Sp, V("h"), Colon, Sp, D(0), Sp, Lt, Sp, V("n"), Sp,
            Q("then"), Sp, Add(Val(App(pi, App(Q("Fin", "mk"), D(0), V("h")))), D(1)),
            Sp, Q("else"), Sp, D(0));
        return positive;
    }
    private static Formula MajorBody() => All("n", Naturals, All("pi", Permutations,
        Equal(Call("maj", V("pi")), Seq(new Formula.Subscript(Sum,
            Seq(V("i"), Colon, Sp, Call("Fin", V("n")))), Sp,
            Parenthesized(Add(Val(V("i")), D(1))), Sp, Cdot, Sp,
            App(Q("D5", "S1", "Words", "Patterns", "Separable", "CutFactorization", "descentAt"),
                V("pi"), V("i"))))));
    private static Formula Slice() => App(Q("Finset", "filter"),
        Parenthesized(Seq(V("pi"), Colon, Sp, Permutations, Sp, Mapsto, Sp,
            Equal(Call("maj", V("pi")), V("k")))),
        Parenthesized(Seq(Q("Finset", "univ"), Colon, Sp, Call("Finset", Permutations))));
    private static Formula Parameters(Formula body) => All("n", Naturals, All("k", Naturals, body));
    private static Formula CountBody() => Parameters(Equal(Call("count", V("n"), V("k")),
        App(Q("Finset", "card"), Slice())));
    private static Formula ExpectationBody() => Parameters(Equal(Call("E", V("n"), V("k")),
        new Formula.Fraction(Seq(new Formula.Subscript(Sum,
            Seq(V("pi"), Sp, InMacro, Sp, Slice())), Sp, Cast(FirstLetterValue(V("pi")))),
            Cast(Call("count", V("n"), V("k"))))));
    private static Formula ClaimBody()
    {
        var polynomial = Call("Polynomial", Rationals);
        var evaluation = All("n", Naturals, Seq(V("k"), Sp, Le, Sp, V("n"), Sp, Implies, Sp,
            Call("count", V("n"), V("k")), Sp, Neq, Sp, D(0), Sp, Implies, Sp,
            Equal(Call("E", V("n"), V("k")), new Formula.Fraction(
                App(Q("Polynomial", "eval"), Cast(V("n")), V("P")),
                Seq(Parenthesized(Seq(Add(Cast(V("k")), D(1)), Colon, Sp, Rationals)), Sp, Cdot, Sp,
                    App(Q("Polynomial", "eval"), Cast(V("n")), V("Q")))))));
        var body = Seq(App(Q("Polynomial", "Monic"), V("P")), Sp, Land, Sp,
            App(Q("Polynomial", "Monic"), V("Q")), Sp, Land, Sp,
            Equal(App(Q("Polynomial", "natDegree"), V("P")), Add(V("k"), D(1))), Sp, Land, Sp,
            Equal(App(Q("Polynomial", "natDegree"), V("Q")), V("k")), Sp, Land, Sp, evaluation);
        body = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("Q"), polynomial, body);
        body = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("P"), polynomial, body);
        return All("k", Naturals, Seq(D(0), Sp, Lt, Sp, V("k"), Sp, Implies, Sp, body));
    }
}
