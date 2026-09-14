using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class CloitrePrimeGapDivisorCharacterizationRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/CloitrePrimeGapDivisorCharacterizationRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/laboselemer2002a049591");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The value 529 refutes Cloitre's divisor-count prime-gap characterization.",
        H("The OEIS A049591 Divisor-Count Prime-Gap Characterization"),
        Blocks(
            Node("a049591-term", "Membership in A049591",
                TermFormula(),
                "A natural n is a term when it is odd and prime while n+2 is not prime.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a049591-no-prime-in-gap", "The prime-free interval condition",
                NoPrimeInGapFormula(),
                "NoPrimeInGap(n) means that no prime lies strictly between n and n plus "
                    + "the square of the number of divisors of n.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a049591-gap-characterization", "Cloitre's characterization",
                ClaimFormula(),
                "The characterization asserts that every natural n greater than one is "
                    + "a sequence term exactly when it satisfies the prime-free interval condition.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a049591-gap-characterization-refuted", "The characterization fails at 529",
                ResultFormula(),
                "The value 529 has exactly three divisors, and every integer strictly between "
                    + "529 and 538 is composite, so NoPrimeInGap(529) holds. But 529 is not "
                    + "prime, so Term(529) fails. This refutes only Cloitre's gap "
                    + "characterization; the sequence definition and the entry's other comments "
                    + "are untouched.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a049591-prime-gap-divisor-characterization-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(
        string id,
        string title,
        Formula formula,
        string prose,
        DescribeRole role,
        AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + DeclarationName(id)),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, claim);

    private static string DeclarationName(string id) => id switch
    {
        "a049591-term" => "Term",
        "a049591-no-prime-in-gap" => "NoPrimeInGap",
        "a049591-gap-characterization" => "claim",
        "a049591-gap-characterization-refuted" => "result",
        _ => throw new ArgumentOutOfRangeException(nameof(id)),
    };

    private static Formula TermFormula()
    {
        var n = F.Id("n");
        var definition = new Formula.Logic(
            Parenthesized(Call("Term", n)),
            FormulaLogicOperator.Iff,
            Parenthesized(And(
                Call("Odd", n),
                Call("Prime", n),
                new Formula.Not(Call("Prime", Add(n, D(2)))))));
        return Disp(Universal("n", definition));
    }

    private static Formula NoPrimeInGapFormula()
    {
        var n = F.Id("n");
        var p = F.Id("p");
        var interval = And(
            Less(n, p),
            Less(p, Add(n, new Formula.Power(
                Call("card", Call("divisors", n)), D(2)))));
        var noPrime = Universal("p", new Formula.Logic(
            Parenthesized(Call("Prime", p)),
            FormulaLogicOperator.Implies,
            Parenthesized(new Formula.Not(Parenthesized(interval)))));
        var definition = new Formula.Logic(
            Parenthesized(Call("NoPrimeInGap", n)),
            FormulaLogicOperator.Iff,
            Parenthesized(noPrime));
        return Disp(Universal("n", definition));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n");
        var equivalence = new Formula.Logic(
            Parenthesized(Call("Term", n)),
            FormulaLogicOperator.Iff,
            Parenthesized(Call("NoPrimeInGap", n)));
        var quantified = Universal("n", new Formula.Logic(
            Parenthesized(Less(D(1), n)),
            FormulaLogicOperator.Implies,
            Parenthesized(equivalence)));
        return Disp(new Formula.Logic(
            Parenthesized(F.Id("claim")),
            FormulaLogicOperator.Iff,
            Parenthesized(quantified)));
    }

    private static Formula ResultFormula() =>
        Disp(new Formula.Not(F.Id("claim")));

    private static Formula Universal(string variable, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(variable),
            Naturals(),
            body);

    private static Formula And(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (int i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(
                Parenthesized(clauses[i]), FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
