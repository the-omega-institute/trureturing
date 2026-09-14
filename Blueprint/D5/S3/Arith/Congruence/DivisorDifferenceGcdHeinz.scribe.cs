using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class DivisorDifferenceGcdHeinzDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Congruence/DivisorDifferenceGcdHeinz.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/wiseman2019a258409");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every n at least two, the divisor-minus-one gcd agrees with the gcd of "
            + "successive divisor gaps and with the prime-index gcd of their Heinz number.",
        H("Wiseman's Divisor-Difference GCD Identity"),
        Blocks(
            Paragraph(Text(
                "For every n at least two, the positive divisors are read in increasing order. "
                    + "Natural subtraction forms each successive gap, and prime indices are "
                    + "one-based, so prime(1)=2 is encoded by Nat.nth Nat.Prime 0.")),
            Node(
                "a",
                "The divisor-minus-one gcd",
                AFormula(),
                "For every n at least two, a(n) is the gcd of d-1 over all positive divisors d of n.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Factorization/wiseman2019a258409"))),
            Node(
                "consecutiveDivisorDifferences",
                "Successive divisor differences",
                ConsecutiveDivisorDifferencesFormula(),
                "For every n at least two, this list applies the binary map (x,y) to y-x to the "
                    + "increasing divisor list and its tail, retaining the multiplicity of equal gaps.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "consecutiveDifferenceGcd",
                "The gcd of successive divisor differences",
                ConsecutiveDifferenceGcdFormula(),
                "For every n at least two, this is the gcd of the finite set underlying the list "
                    + "of successive divisor gaps; repeated gaps do not change the gcd.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "heinzDifferences",
                "The Heinz number of the divisor gaps",
                HeinzDifferencesFormula(),
                "For every n at least two, this is the product of prime(delta) over the full list "
                    + "of successive gaps delta. The source uses one-based prime indices, while "
                    + "the Lean definition encodes prime(delta) as Nat.nth Nat.Prime (delta-1).",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "primeIndexGcd",
                "The gcd of prime indices",
                PrimeIndexGcdFormula(),
                "For every n at least two and m=heinzDifferences(n), this is the gcd of the "
                    + "one-based indices of all prime factors of m.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "wiseman_a258409",
                "Wiseman's three-term identity",
                WisemanFormula(),
                "For every n at least two, a(n) equals both the prime-index gcd obtained by "
                    + "decoding the Heinz number of the gaps and the gcd of the gaps themselves. "
                    + "The first equality follows because the prime factors of the product are "
                    + "exactly the primes indexed by the gaps. For the second equality, a common "
                    + "divisor of every d-1 divides every successive difference, while a common "
                    + "divisor of the gaps divides each d-1 by telescoping from the first divisor 1.",
                DescribeRole.Theorem,
                AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a258409-divisor-difference-gcd-heinz"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(
        string name,
        string title,
        Formula formula,
        string prose,
        DescribeRole role,
        AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
            DescribeId.Create("a258409-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role,
            claim);

    private static Formula AFormula()
    {
        Formula n = F.Id("n");
        Formula d = F.Id("d");
        Formula values = new Formula.SetBuilder(
            Subtract(d, D(1)), d, Call("divisors", n));
        return Universal("n", Equal(Call("a", n), Call("gcd", values)));
    }

    private static Formula ConsecutiveDivisorDifferencesFormula()
    {
        Formula n = F.Id("n");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula divisors = Call("sort", Call("divisors", n));
        return Universal("n", Equal(
            Call("consecutiveDivisorDifferences", n),
            Call("zipWith", Parenthesized(Subtract(y, x)), divisors, Call("tail", divisors))));
    }

    private static Formula ConsecutiveDifferenceGcdFormula()
    {
        Formula n = F.Id("n");
        return Universal("n", Equal(
            Call("consecutiveDifferenceGcd", n),
            Call("gcd", Call("toFinset", Call("consecutiveDivisorDifferences", n)))));
    }

    private static Formula HeinzDifferencesFormula()
    {
        Formula n = F.Id("n");
        Formula delta = F.Id("d");
        Formula index = Member(delta, Call("consecutiveDivisorDifferences", n));
        Formula product = Seq(
            new Formula.Subscript(F.Prod, index),
            Sp,
            Call("prime", delta));
        return Universal("n", Equal(Call("heinzDifferences", n), product));
    }

    private static Formula PrimeIndexGcdFormula()
    {
        Formula m = F.Id("m");
        Formula p = F.Id("p");
        Formula indices = new Formula.SetBuilder(
            Call("primeIndex", p), p, Call("primeFactors", m));
        return Universal("m", Equal(Call("primeIndexGcd", m), Call("gcd", indices)));
    }

    private static Formula WisemanFormula()
    {
        Formula n = F.Id("n");
        Formula first = Equal(
            Call("a", n),
            Call("primeIndexGcd", Call("heinzDifferences", n)));
        Formula second = Equal(
            Call("a", n),
            Call("consecutiveDifferenceGcd", n));
        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("n"), Naturals())],
            Implies(LessOrEqual(D(2), n), Parenthesized(And(first, second)))));
    }

    private static Formula Universal(string name, Formula body) => Disp(new Formula.BindMany(
        FormulaQuantifier.ForAll,
        [new Formula.BoundVariable(FormulaIdentifier.Create(name), Naturals())],
        body));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Relation(
        Formula left, FormulaRelationOperator relation, Formula right) =>
        new Formula.Relation(left, relation, right);

    private static Formula Equal(Formula left, Formula right) =>
        Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Member(Formula left, Formula right) =>
        Relation(left, FormulaRelationOperator.MemberOf, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Naturals() => F.Id("N");
}
