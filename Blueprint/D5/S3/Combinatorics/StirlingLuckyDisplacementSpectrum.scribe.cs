using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class StirlingLuckyDisplacementSpectrumDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/StirlingLuckyDisplacementSpectrum.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/colmenarejo2024lucky");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every count of unlucky cars allowed by the bound is attained by a Stirling permutation.",
        H("The Unlucky-Car Spectrum of Stirling Permutations"),
        Blocks(
            Node("free-from-definition", "Walking up to a free spot", "freeFrom",
                FreeFromFormula(),
                "A bounded upward search: from the spot s, move on while the spot is taken, "
                    + "and stop after at most f moves. The bound f is supplied by the caller "
                    + "and is chosen below so that the search always stops at a free spot.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("occ-bound-definition", "A bound for the occupied spots", "occBound",
                OccBoundFormula(),
                "The largest of p and the entries of occ. Every occupied spot is at most this "
                    + "value, so the first free spot at or after p is at most one more than it.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("first-free-definition", "The spot a car takes", "firstFree",
                FirstFreeFormula(),
                "The source has each car drive to its preferred spot and then continue forward "
                    + "to the first free spot. Running the upward search with one more step "
                    + "than the bound of the occupied spots reaches that spot in every case: "
                    + "if p exceeds every occupied spot the search stops at once, and "
                    + "otherwise the first free spot at or after p is at most the bound plus "
                    + "one, which is within reach.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("park-aux-definition", "Parking the cars in order", "parkAux",
                ParkAuxFormula(),
                "Cars enter one at a time, each taking the first free spot at or after the one "
                    + "it prefers, and the list records the spot each car takes.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("spots-definition", "Parking on an empty lot", "spots",
                SpotsFormula(),
                "The parking outcome of the word w, read as a preference list on an initially "
                    + "empty lot with spots numbered from one.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("dis-definition", "The displacement composition", "dis",
                DisFormula(),
                "Definition 39 of the source: the tuple whose entry for each car is the spot "
                    + "the car takes minus the spot it prefers. A car is lucky exactly when "
                    + "its entry is zero, so the number of nonzero entries is the number of "
                    + "unlucky cars. Every Stirling permutation is a parking function, so each "
                    + "entry is a difference of a larger spot from a smaller preference.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("displaced-definition", "Counting the unlucky cars", "displaced",
                DisplacedFormula(),
                "The number of nonzero entries of the displacement composition. Corollary 41 "
                    + "of the source bounds this count between n and 2n minus one for every "
                    + "Stirling permutation of order n, because the number of lucky cars lies "
                    + "between one and n.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("stirling-definition", "Stirling permutations", "IsStirling",
                IsStirlingFormula(),
                "Definition 4 of the source reads verbatim: \"A permutation of the multiset "
                    + "{1, 1, 2, 2, 3, 3, . . . , n, n} is a Stirling permutation of order n if "
                    + "every value j appearing between the two instances of i satisfies "
                    + "j > i.\" Being a permutation of that multiset is recorded by the length "
                    + "and by the letter counts, which are two for each value from one to n "
                    + "and zero for every other value. The condition on values between two "
                    + "equal letters is recorded by the absence of a subsequence v, u, v with "
                    + "u at most v: such a subsequence is exactly a value at most i standing "
                    + "between two occurrences of i.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("problem-statement", "The question asked of the spectrum", "claim",
                ClaimFormula(),
                "Problem 48 of the source reads verbatim: \"Determine if, for i in [n, 2n - 1], "
                    + "there exists w in Q_n such that dis(w) has exactly i nonzero entries. "
                    + "Equivalently, can we always find a Stirling permutation with i unlucky "
                    + "cars?\" The statement displayed here is the affirmative reading of that "
                    + "question, quantified over every order n at least one and every count i "
                    + "in the stated range.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("spectrum-attained", "Every allowed count is attained", "result",
                ResultFormula(),
                "The answer is yes, by an explicit two-block word. For j from zero to n minus "
                    + "one, take the word that lists the pairs j+1, j+2, up to n in increasing "
                    + "order and then the pairs j, j-1, down to 1 in decreasing order, each "
                    + "value written twice in succession. Equal letters are adjacent, so no "
                    + "value stands between two equal letters and the word is a Stirling "
                    + "permutation of order n. The occupied spots form one interval at every "
                    + "stage of parking. The first car takes spot j+1 and is lucky; each "
                    + "further car of the increasing block finds its preference inside the "
                    + "occupied interval and is pushed to the spot just above it, so after the "
                    + "increasing block the occupied spots are j+1 through 2n-j and exactly "
                    + "one car has been lucky. In the decreasing block the first copy of each "
                    + "value v lands on the free spot v just below the interval and is lucky, "
                    + "while the second copy is pushed to the spot just above it, so each of "
                    + "the j pairs contributes one lucky car and the interval grows by one at "
                    + "each end. The lot ends full, spots 1 through 2n, with j+1 lucky cars "
                    + "and therefore 2n-j-1 nonzero displacement entries. As j runs from zero "
                    + "to n minus one this count runs over every value from n to 2n-1, so "
                    + "choosing j equal to 2n-1-i answers the question for the count i.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("stirling-lucky-displacement-spectrum"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role,
            resolution);

    private static Formula FreeFromFormula()
    {
        Formula occ = F.Id("occ"), s = F.Id("s"), f = F.Id("f");
        Formula basis = Equal(Call("freeFrom", D(0), occ, s), s);
        Formula taken = Implies(Member(s, occ),
            Equal(Call("freeFrom", Add(f, D(1)), occ, s),
                Call("freeFrom", f, occ, Add(s, D(1)))));
        Formula freeSpot = Implies(NotMember(s, occ),
            Equal(Call("freeFrom", Add(f, D(1)), occ, s), s));
        return Disp(Universal("occ", ListOfNaturals(),
            Universal("s", Naturals(),
                Universal("f", Naturals(),
                    Seq(basis, Sp, Sp, Sp, And(taken, freeSpot))))));
    }

    private static Formula OccBoundFormula()
    {
        Formula occ = F.Id("occ"), p = F.Id("p");
        return Disp(Universal("occ", ListOfNaturals(),
            Universal("p", Naturals(),
                Equal(Call("occBound", occ, p), Call("foldr", F.Id("max"), p, occ)))));
    }

    private static Formula FirstFreeFormula()
    {
        Formula occ = F.Id("occ"), p = F.Id("p");
        return Disp(Universal("occ", ListOfNaturals(),
            Universal("p", Naturals(),
                Equal(Call("firstFree", occ, p),
                    Call("freeFrom", Add(Call("occBound", occ, p), D(1)), occ, p)))));
    }

    private static Formula ParkAuxFormula()
    {
        Formula occ = F.Id("occ"), p = F.Id("p"), ps = F.Id("ps");
        Formula spot = Call("firstFree", occ, p);
        Formula basis = Equal(Call("parkAux", Nil(), occ), Nil());
        Formula recursion = Equal(Call("parkAux", Cons(p, ps), occ),
            Cons(spot, Call("parkAux", ps, Cons(spot, occ))));
        return Disp(Universal("occ", ListOfNaturals(),
            Universal("p", Naturals(),
                Universal("ps", ListOfNaturals(),
                    Seq(basis, Sp, Sp, Sp, recursion)))));
    }

    private static Formula SpotsFormula()
    {
        Formula w = F.Id("w");
        return Disp(Universal("w", ListOfNaturals(),
            Equal(Call("spots", w), Call("parkAux", w, Nil()))));
    }

    private static Formula DisFormula()
    {
        Formula w = F.Id("w"), s = F.Id("s"), p = F.Id("p");
        Formula rule = Seq(Open, s, Comma, Sp, p, Close, Sp, Mapsto, Sp, Subtract(s, p));
        return Disp(Universal("w", ListOfNaturals(),
            Equal(Call("dis", w), Call("zipWith", rule, Call("spots", w), w))));
    }

    private static Formula DisplacedFormula()
    {
        Formula w = F.Id("w"), d = F.Id("d");
        Formula rule = Seq(d, Sp, Mapsto, Sp, NotEqual(d, D(0)));
        return Disp(Universal("w", ListOfNaturals(),
            Equal(Call("displaced", w), Call("countP", rule, Call("dis", w)))));
    }

    private static Formula IsStirlingFormula()
    {
        Formula n = F.Id("n"), w = F.Id("w"), v = F.Id("v"), u = F.Id("u");
        Formula inRange = And(LessEqual(D(1), v), LessEqual(v, n));
        Formula lengthClause = Equal(Call("length", w), Multiply(D(2), n));
        Formula countClause = Universal("v", Naturals(),
            And(Implies(inRange, Equal(Call("count", w, v), D(2))),
                Implies(Negated(inRange), Equal(Call("count", w, v), D(0)))));
        Formula patternClause = Universal("v", Naturals(),
            Universal("u", Naturals(),
                Implies(LessEqual(u, v),
                    Negated(Call("Sublist", Triple(v, u, v), w)))));
        return Disp(Universal("n", Naturals(),
            Universal("w", ListOfNaturals(),
                Iff(Call("IsStirling", n, w),
                    And(lengthClause, And(countClause, patternClause))))));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), i = F.Id("i"), w = F.Id("w");
        Formula conclusion = Exists("w", ListOfNaturals(),
            And(Call("IsStirling", n, w), Equal(Call("displaced", w), i)));
        Formula body = Universal("n", Naturals(),
            Implies(LessEqual(D(1), n),
                Universal("i", Naturals(),
                    Implies(LessEqual(n, i),
                        Implies(LessEqual(i, Subtract(Multiply(D(2), n), D(1))),
                            conclusion)))));
        return Disp(Iff(F.Id("claim"), body));
    }

    private static Formula ResultFormula() => Disp(F.Id("claim"));

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula ListOfNaturals() => Call("List", Naturals());

    private static Formula Nil() => Seq(OpenBracket, CloseBracket);

    private static Formula Cons(Formula head, Formula tail) =>
        Seq(head, Sp, Colon, Colon, Sp, tail);

    private static Formula Triple(Formula a, Formula b, Formula c) =>
        Seq(OpenBracket, a, Comma, Sp, b, Comma, Sp, c, CloseBracket);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Negated(Formula value) =>
        new Formula.Not(Parenthesized(value));

    private static Formula Member(Formula element, Formula collection) =>
        Seq(element, Sp, InMacro, Sp, collection);

    private static Formula NotMember(Formula element, Formula collection) =>
        Negated(Member(element, collection));

    private static Formula Universal(string name, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
}
