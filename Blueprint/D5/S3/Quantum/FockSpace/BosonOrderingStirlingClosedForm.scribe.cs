using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FockSpace;

internal sealed class BosonOrderingStirlingClosedFormDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/FockSpace/BosonOrderingStirlingClosedForm.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Quantum/maier2024bosonordering");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The generalized Stirling numbers with parameters (-1, 2; r), which govern boson operator orderings, have the closed form conjectured by Maier for every integer r, once the first binomial coefficient is read as the generalized binomial coefficient.",
        H("A closed form for the generalized Stirling numbers of boson ordering"),
        Blocks(
            Node("stirling", "The numbers S-hat", StirlingFormula(),
                "Theorem 4.1 of the source: for alpha = -1 and beta = 2 the number S-hat(n, k; r) is the k-th forward difference at x = 0 of the rising factorial (2x + r)(2x + r + 1) ... (2x + r + n - 1).",
                "stirlingHat", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("sum", "The conjectured sum", SumFormula(),
                "The sum over integers j from floor((2 - r)/2) to floor((n + 2 - r)/2) of the generalized binomial coefficient C(n - j, n - k), times n! and the ordinary binomial coefficient C(n + 1, 2j + r - 1), whose lower index lies between 0 and n + 1 in this range.",
                "conjectureSum", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjecture", ClaimDefinitionFormula(),
                "Conjecture 5.3 of the source, for all n, all k <= n and all integers r. The source notes that the upper argument n - j may be negative; with the convention that a binomial coefficient with negative upper argument vanishes, the identity fails already at n = 1, k = 1, r = -1.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Proof of the conjecture", Disp(F.Id("claim")),
                "Extend the sum to all integers j; the terms outside the range vanish. Both sides f(n, k, r) satisfy f(n, k + 1, r) = f(n, k, r + 2) - f(n, k, r) for k < n: on the left because forward differences commute with the shift x -> x + 1, which sends r to r + 2; on the right by shifting j and Pascal's rule for the generalized binomial coefficient. At k = 0 the left side is the rising factorial of r, and both sides satisfy f(n + 1, 0, r) - f(n + 1, 0, r - 1) = (n + 1) f(n, 0, r): on the left because the rising factorials of r and r - 1 share n factors, on the right by Pascal's rule applied twice and a shift of j. At r = 1 both sides equal n!, that is f(n, 0, 1) = n! for every n, so induction on n and then on the integer r settles k = 0, and induction on k settles every k <= n.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("maier-2024-boson-ordering-stirling-closed-form"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("maier-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Named(string name)
    {
        var tokens = new List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (tokens.Count > 0) tokens.Add(Dot);
            tokens.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. tokens])));
    }
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Times(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula SumOver(string variable, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(F.Id(variable), Sp, InMacro, Sp, domain)), Sp, body);

    private static Formula StirlingFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k"), r = F.Id("r"), x = F.Id("x");
        Formula term = Times(Times(new Formula.Power(Parenthesized(new Formula.Negate(D(1))), Subtract(k, x)),
            Call("choose", k, x)), Call("rising", Add(Times(D(2), x), r), n));
        return Disp(Equal(Call("stirlingHat", n, k, r), SumOver("x", Call("range", Add(k, D(1))), term)));
    }

    private static Formula SumFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k"), r = F.Id("r"), j = F.Id("j");
        Formula lower = new Formula.Floor(new Formula.Fraction(Subtract(D(2), r), D(2)));
        Formula upper = new Formula.Floor(new Formula.Fraction(Subtract(Add(n, D(2)), r), D(2)));
        Formula term = Times(Times(Call("Ring.choose", Subtract(n, j), Subtract(n, k)), Call("factorial", n)),
            Call("choose", Add(n, D(1)), Subtract(Add(Times(D(2), j), r), D(1))));
        return Disp(Equal(Call("conjectureSum", n, k, r), SumOver("j", Call("Icc", lower, upper), term)));
    }

    private static Formula ClaimBody()
    {
        Formula n = F.Id("n"), k = F.Id("k"), r = F.Id("r");
        return All("n", Naturals(), All("k", Naturals(), Implies(AtMost(k, n),
            All("r", Integers(), Equal(Call("stirlingHat", n, k, r), Call("conjectureSum", n, k, r))))));
    }

    private static Formula ClaimDefinitionFormula() => Disp(
        new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody())));
}
