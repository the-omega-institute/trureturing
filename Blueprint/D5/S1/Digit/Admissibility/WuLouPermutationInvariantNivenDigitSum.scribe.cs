using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Admissibility;

internal sealed class WuLouPermutationInvariantNivenDigitSumDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Digit/Admissibility/WuLouPermutationInvariantNivenDigitSum.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Digit/wu2025pinn");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Wu and Lou's permutation-invariant decimal Niven digit-sum bound.",
        H("Permutation-Invariant Niven Digit-Sum Bound"),
        Blocks(
            Paragraph(Text(
                "DecimalPINN is the source-faithful object: a nonempty list of decimal digits "
                + "whose digit sum divides the Nat.ofDigits value of every list permutation.")),
            Node(
                "DecimalPINN",
                "Permutation-invariant decimal Niven number",
                "The structure records a nonempty decimal digit list, its nonzero leading digit, "
                    + "the bound that every digit is below ten, and divisibility of every "
                    + "permuted Nat.ofDigits value by the source digit sum.",
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source)),
            Node(
                "result",
                "Distinct-digit digit-sum bound",
                ResultFormula(),
                "For at least two nonzero digit occurrences and at least two distinct digit "
                    + "values, the digit sum is divisible by three, is at least three, and is "
                    + "at most 81. The divisibility-by-three clause is literature-attested by "
                    + "Wu and Lou's Theorem 1 consequence in section 8.4; the lower bound follows "
                    + "from positivity; the upper bound is the repository-derived settlement of "
                    + "the conjectural bound. The formal proof reuses the source object's "
                    + "permutation-divisibility field and arithmetic normalization.",
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("wu-lou-permutation-invariant-niven-digit-sum-bound"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(
        string declaration,
        string title,
        string prose,
        DescribeRole role,
        AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("wu-lou-" + declaration.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + declaration),
        H(title),
        StatementSource.WithoutFormula(),
        provenance,
        Blocks(Paragraph(Text(prose))),
        role,
        claim);

    private static DocumentBlock Node(
        string declaration,
        string title,
        Formula formula,
        string prose,
        DescribeRole role,
        AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("wu-lou-" + declaration.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + declaration),
        H(title),
        StatementSource.FromAuthor(formula),
        provenance,
        Blocks(Paragraph(Text(prose))),
        role,
        claim);

    private static Formula ResultFormula()
    {
        var d = F.Id("d");
        var digits = Call("digits", d);
        var sum = Call("sum", digits);
        var nonzeroCount = Call("countP", digits,
            Lambda(F.Id("x"), NotEqual(F.Id("x"), D(0))));
        var distinct = Existential("a", digits,
            Existential("b", digits, NotEqual(F.Id("a"), F.Id("b"))));
        var conclusion = And(
            Divides(D(3), sum),
            And(LessOrEqual(D(3), sum), LessOrEqual(sum, D(8, 1))));
        return Disp(Universal("d", F.Id("DecimalPINN"),
            Implies(
                Parenthesized(LessOrEqual(D(2), nonzeroCount)),
                Implies(Parenthesized(distinct), Parenthesized(conclusion)))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Lambda(Formula variable, Formula body) =>
        Parenthesized(Seq(variable, Sp, Mapsto, Sp, body));

    private static Formula Universal(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);

    private static Formula Existential(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Divides(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Divides, right);
}
