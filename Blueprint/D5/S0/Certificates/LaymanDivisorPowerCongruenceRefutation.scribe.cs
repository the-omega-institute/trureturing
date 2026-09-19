using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class LaymanDivisorPowerCongruenceRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/LaymanDivisorPowerCongruenceRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/layman2011a196226");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The integer 690 refutes John W. Layman's three divisor-power congruence conjectures.",
        H("Layman's OEIS A196226 Divisor-Power Congruence Conjectures"),
        Blocks(
            Node("a196226-membership", "Membership in OEIS A196226",
                MembershipFormula(),
                "A natural number m is a member when it is even and the remainder of "
                    + "sigma sub one of m modulo m equals 3 + m/2. Here slash denotes "
                    + "natural-number integer division; the divisibility clause makes m/2 exact.",
                "membership", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("a196226-layman-congruences", "Layman's three congruence conjectures",
                ClaimFormula(),
                "The claim is the disjunction of the three published universal congruences. "
                    + "Their thresholds are 14, 22, and 38; their divisor-power exponents are "
                    + "2, 3, and 4; and their constants are 5, 9, and 17. Nat.ModEq(m,x,y) "
                    + "means that x and y are congruent modulo m, and every slash denotes "
                    + "natural-number integer division.",
                "claim", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("a196226-layman-congruences-refuted", "All three conjectures are false",
                ResultFormula(),
                "At m = 690, sigma sub one is 1728, so the membership remainder is 348. "
                    + "The next three divisor-power sums are 689000, 386358336, and "
                    + "244202442248. Their remainders modulo 690 are 380, 426, and 668, "
                    + "rather than the required 350, 354, and 362. Thus each disjunct fails.",
                "result", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a196226-layman-divisor-power-congruences"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(
        string id,
        string title,
        Formula formula,
        string prose,
        string declaration,
        DescribeRole role,
        AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula MembershipFormula()
    {
        var m = F.Id("m");
        var half = NatDivide(m, D(2));
        var membership = And(
            Divides(D(2), m),
            Equal(
                new Formula.Modulo(Sigma(D(1), m), m),
                Add(D(3), half)));
        return Disp(Universal("m", Iff(Call("membership", m), membership)));
    }

    private static Formula ClaimFormula()
    {
        var clauseTwo = CongruenceClause(14, 2, 5);
        var clauseThree = CongruenceClause(22, 3, 9);
        var clauseFour = CongruenceClause(38, 4, 17);
        return Disp(Iff(F.Id("claim"), Or(clauseTwo, clauseThree, clauseFour)));
    }

    private static Formula CongruenceClause(int threshold, int exponent, int constant)
    {
        var m = F.Id("m");
        var premise = And(
            Call("membership", m),
            LessThanOrEqual(Digits(threshold), m));
        var conclusion = QualifiedCall(
            "Nat", "ModEq", m, Sigma(Digits(exponent), m),
            Add(Digits(constant), NatDivide(m, D(2))));
        return Universal("m", Implies(premise, conclusion));
    }

    private static Formula ResultFormula() =>
        Disp(new Formula.Not(F.Id("claim")));

    private static Formula Sigma(Formula exponent, Formula value) =>
        QualifiedCall("ArithmeticFunction", "sigma", exponent, value);

    private static Formula NatDivide(Formula numerator, Formula denominator) =>
        Parenthesized(Seq(numerator, Sp, Slash, Sp, denominator));

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

    private static Formula Or(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (int i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(
                Parenthesized(clauses[i]), FormulaLogicOperator.Or, result);
        return result;
    }

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessThanOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Divides(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Divides, right);

    private static Formula QualifiedCall(
        string prefix,
        string name,
        params Formula[] arguments) =>
        new Formula.Apply(Seq(F.Id(prefix), Dot, F.Id(name)), [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Parenthesized(Formula value) =>
        Seq(Open, value, Close);

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Digits(int value) =>
        D(value.ToString(System.Globalization.CultureInfo.InvariantCulture)
            .Select(character => (byte)(character - '0'))
            .ToArray());
}
