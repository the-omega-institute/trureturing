using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class CohenConsecutiveCubePrimePairThresholdRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/CohenConsecutiveCubePrimePairThresholdRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/cohen2025cyclic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The printed thresholds in Cohen's Conjectures 28 and 29 fail at n = 11 and n = 12.",
        H("Cohen's Consecutive-Cube Prime-Pair Thresholds"),
        Blocks(
            Node(
                "cohen-twin-pair-count",
                "Twin-prime pairs between consecutive cubes",
                "twinPairCount",
                TwinPairCountFormula(),
                "For each natural n, the half-open finite interval starts at n^3 + 1. "
                    + "The filter retains exactly the p for which n^3 < p, p + 2 < (n+1)^3, "
                    + "and both p and p + 2 are prime; its cardinality is twinPairCount(n).",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "cohen-cousin-pair-count",
                "Cousin-prime pairs between consecutive cubes",
                "cousinPairCount",
                CousinPairCountFormula(),
                "For each natural n, the filter requires n^3 < p and p + 4 < (n+1)^3. "
                    + "It also requires p and p + 4 to be prime and p + 1, p + 2, and p + 3 "
                    + "not to be prime, so the endpoint primes are consecutive.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "cohen-conjecture-twenty-eight",
                "Conjecture 28",
                "claim28",
                Claim28Formula(),
                "The paper states: \"Conjecture 28 (number of twin primes between consecutive "
                    + "cubes). For every n ∈ N, the number of pairs of twin primes between n³ "
                    + "and (n + 1)³ is never less than two. More generally, for every k ∈ N, "
                    + "there exists N(k) ∈ N such that for all n ≥ N(k) there are at least k pairs "
                    + "of twin primes between n³ and (n + 1)³. Specifically, N(1) = N(2) = 1, "
                    + "N(3) = 3, N(4) = 5, N(5) = 8, N(6) = N(7) = N(8) = N(9) = 10, "
                    + "N(10) = 11, N(11) = 13, N(12) = N(13) = N(14) = N(15) = N(16) = 15, "
                    + "and N(17) = 20.\" Each printed threshold is represented as its own "
                    + "universal conjunct. The existential N ranges over natural numbers; adding "
                    + "1 ≤ N would strengthen that unused conjunct and does not affect the refutation.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "cohen-conjecture-twenty-nine",
                "Conjecture 29",
                "claim29",
                Claim29Formula(),
                "The paper states: \"Conjecture 29 (number of cousin primes between consecutive "
                    + "cubes). For n ∈ N with n > 1, the number of pairs of cousin primes between "
                    + "n³ and (n + 1)³ is never less than two. More generally, for every k ∈ N, "
                    + "there exists N(k) ∈ N such that, for all n ≥ N(k), there are at least k pairs "
                    + "of cousin primes between n³ and (n + 1)³. Specifically, N(1) = N(2) = 2, "
                    + "N(3) = 8, N(4) = N(5) = N(6) = N(7) = 9, N(8) = N(9) = N(10) = 12.\" "
                    + "Each printed threshold is represented as its own universal conjunct. The "
                    + "existential N ranges over natural numbers; adding 1 ≤ N would strengthen that "
                    + "unused conjunct and does not affect the refutation.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "cohen-conjecture-twenty-eight-refuted",
                "Conjecture 28 is false",
                "result28",
                ResultFormula("claim28"),
                "At n = 11 the open interval (1331,1728) contains exactly nine twin-prime "
                    + "pairs: (1427,1429), (1451,1453), (1481,1483), (1487,1489), "
                    + "(1607,1609), (1619,1621), (1667,1669), (1697,1699), and "
                    + "(1721,1723). Thus the printed N(10) = 11 threshold is false.",
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "cohen-consecutive-cube-twin-prime-threshold-refutation"),
                    ResolutionKind.Refuted)),
            Node(
                "cohen-conjecture-twenty-nine-refuted",
                "Conjecture 29 is false",
                "result29",
                ResultFormula("claim29"),
                "At n = 12 the open interval (1728,2197) contains exactly seven cousin-prime "
                    + "pairs: (1783,1787), (1867,1871), (1873,1877), (1993,1997), "
                    + "(1999,2003), (2083,2087), and (2137,2141). Thus the printed "
                    + "N(8) = N(9) = N(10) = 12 thresholds are false.",
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "cohen-consecutive-cube-cousin-prime-threshold-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(
        string id,
        string title,
        string declaration,
        Formula formula,
        string prose,
        DescribeRole role,
        AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role,
            resolution);

    private static Formula TwinPairCountFormula() =>
        CountFormula("twinPairCount", 2, consecutive: false);

    private static Formula CousinPairCountFormula() =>
        CountFormula("cousinPairCount", 4, consecutive: true);

    private static Formula CountFormula(string name, int gap, bool consecutive)
    {
        var n = F.Id("n");
        var p = F.Id("p");
        var upper = Power(Parenthesized(Add(n, D(1))), D(3));
        var interval = QualifiedCall(
            "Finset", "Ico", Add(Power(n, D(3)), D(1)), upper);
        var clauses = new List<Formula>
        {
            Less(Add(p, N(gap)), upper),
            Prime(p),
            Prime(Add(p, N(gap)))
        };
        if (consecutive)
        {
            clauses.Add(new Formula.Not(Prime(Add(p, D(1)))));
            clauses.Add(new Formula.Not(Prime(Add(p, D(2)))));
            clauses.Add(new Formula.Not(Prime(Add(p, D(3)))));
        }

        var filtered = QualifiedCall(
            "Finset", "filter", interval, Lambda(p, Conjoin([.. clauses])));
        var count = QualifiedCall("Finset", "card", filtered);
        var equation = Equal(
            Seq(Call(name, n), Colon, Sp, Naturals()),
            count);
        return Disp(Universal("n", equation));
    }

    private static Formula Claim28Formula() => ClaimFormula(
        "claim28",
        "twinPairCount",
        firstIndex: 1,
        [
            (1, 1), (2, 1), (3, 3), (4, 5), (5, 8),
            (6, 10), (7, 10), (8, 10), (9, 10), (10, 11),
            (11, 13), (12, 15), (13, 15), (14, 15), (15, 15),
            (16, 15), (17, 20)
        ]);

    private static Formula Claim29Formula() => ClaimFormula(
        "claim29",
        "cousinPairCount",
        firstIndex: 2,
        [
            (1, 2), (2, 2), (3, 8), (4, 9), (5, 9),
            (6, 9), (7, 9), (8, 12), (9, 12), (10, 12)
        ]);

    private static Formula ClaimFormula(
        string claimName,
        string countName,
        int firstIndex,
        (int k, int threshold)[] thresholds)
    {
        var clauses = new List<Formula>
        {
            ThresholdClause(countName, 2, firstIndex),
            EventualClause(countName)
        };
        foreach (var (k, threshold) in thresholds)
            clauses.Add(ThresholdClause(countName, k, threshold));

        return Disp(Iff(F.Id(claimName), Conjoin([.. clauses])));
    }

    private static Formula ThresholdClause(string countName, int k, int threshold)
    {
        var n = F.Id("n");
        return Universal("n", Implies(
            LessThanOrEqual(N(threshold), n),
            LessThanOrEqual(N(k), Call(countName, n))));
    }

    private static Formula EventualClause(string countName)
    {
        var k = F.Id("k");
        var n = F.Id("n");
        var threshold = F.Id("N");
        var tail = Universal("n", Implies(
            LessThanOrEqual(threshold, n),
            LessThanOrEqual(k, Call(countName, n))));
        return Universal("k", Implies(
            LessThanOrEqual(D(1), k),
            Existential("N", tail)));
    }

    private static Formula ResultFormula(string claimName) =>
        Disp(new Formula.Not(F.Id(claimName)));

    private static Formula Universal(string variable, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(variable),
            Naturals(),
            body);

    private static Formula Existential(string variable, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create(variable),
            Naturals(),
            body);

    private static Formula Conjoin(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (var index = clauses.Length - 2; index >= 0; index--)
        {
            result = new Formula.Logic(
                Parenthesized(clauses[index]),
                FormulaLogicOperator.And,
                result);
        }
        return result;
    }

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left),
            FormulaLogicOperator.Iff,
            Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left),
            FormulaLogicOperator.Implies,
            Parenthesized(right));

    private static Formula Prime(Formula value) =>
        QualifiedCall("Nat", "Prime", value);

    private static Formula Lambda(Formula variable, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, variable, Sp, Mapsto, Sp, body));

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessThanOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula QualifiedCall(
        string prefix,
        string name,
        params Formula[] arguments) =>
        new Formula.Apply(Seq(F.Id(prefix), Dot, F.Id(name)), [.. arguments]);

    private static Formula Parenthesized(Formula value) =>
        Seq(Open, value, Close);

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula N(int value) =>
        D(value.ToString(System.Globalization.CultureInfo.InvariantCulture)
            .Select(character => (byte)(character - '0'))
            .ToArray());
}
