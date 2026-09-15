using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Mersenne;

internal sealed class KrizekSigmaTauRationalPowerMersenneDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Mersenne/KrizekSigmaTauRationalPowerMersenne.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/laboselemer2013a046528");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Krizek's sigma-tau rational-power condition characterizes products of "
            + "distinct Mersenne primes.",
        H("Krizek's A046528 Characterization"),
        Blocks(
            Paragraph(Text(
                "For every positive n, sigma is the divisor-sum function sigma sub one, "
                    + "and tau is the divisor-count function sigma sub zero.")),
            Node(
                "isMersenneProduct",
                "Products of distinct Mersenne primes",
                IsMersenneProductFormula(),
                "A natural number is a Mersenne product when it is the product over a "
                    + "finite set S of primes p for which p plus one is a positive power "
                    + "of two. The finite set makes the prime factors distinct, and the "
                    + "empty product includes one.",
                DescribeRole.Definition),
            Node(
                "ratPow",
                "The sigma-tau integer-power relation",
                RatPowFormula(),
                "The positive exponents a and b express the rational-power equation "
                    + "without real exponentiation: sigma(n) to b equals tau(n) to a. "
                    + "Here sigma is sigma sub one and tau is sigma sub zero.",
                DescribeRole.Definition),
            Node(
                "result",
                "Krizek's rational-power characterization",
                ResultFormula(),
                "Equality of positive powers gives the same prime support for sigma and "
                    + "tau. A largest-odd-prime argument, geometric sums, multiplicative "
                    + "orders in finite residue fields, and a multiplicity-one calculation "
                    + "force tau to be a power of two. The attributed "
                    + "Sivaramakrishnan-Shallit prerequisite then identifies n as a product "
                    + "of distinct Mersenne primes. Conversely, multiplicativity gives the "
                    + "required exponents. Only this equivalence is proved.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a046528-sigma-tau-rational-power-mersenne-characterization"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(
        string name,
        string title,
        Formula formula,
        string prose,
        DescribeRole role,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a046528-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name),
        H(title),
        StatementSource.FromAuthor(formula),
        role is DescribeRole.Definition
            ? AssessedProvenance.FromLiterature(Source)
            : AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))),
        role,
        claim);

    private static Formula IsMersenneProductFormula()
    {
        Formula n = F.Id("n");
        Formula s = F.Id("S");
        Formula p = F.Id("p");
        Formula k = F.Id("k");
        Formula product = Seq(
            new Formula.Subscript(Prod, Seq(p, Sp, InMacro, Sp, s)),
            Sp,
            p);
        Formula mersennePrime = And(
            Call("Prime", p),
            ExistsMany(
                [Bound("k", Naturals())],
                And(
                    Lt(D(0), k),
                    Equal(Add(p, D(1)), Pow(D(2), k)))));
        Formula allFactors = ForAll(
            [Bound("p", Naturals())],
            Implies(Member(p, s), mersennePrime));
        Formula representation = ExistsMany(
            [Bound("S", Call("Finset", Naturals()))],
            And(Equal(n, product), allFactors));
        return Disp(ForAll(
            [Bound("n", Naturals())],
            Iff(Call("isMersenneProduct", n), representation)));
    }

    private static Formula RatPowFormula()
    {
        Formula n = F.Id("n");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula powers = Equal(
            Pow(Call("sigma", n), b),
            Pow(Call("tau", n), a));
        Formula existence = ExistsMany(
            [Bound("a", Naturals()), Bound("b", Naturals())],
            And(Le(D(1), a), And(Le(D(1), b), powers)));
        return Disp(ForAll(
            [Bound("n", Naturals())],
            Iff(Call("ratPow", n), existence)));
    }

    private static Formula ResultFormula()
    {
        Formula n = F.Id("n");
        return Disp(ForAll(
            [Bound("n", Naturals())],
            Implies(
                Le(D(1), n),
                Iff(Call("isMersenneProduct", n), Call("ratPow", n)))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula ExistsMany(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Pow(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Naturals() =>
        Seq(Mathbb, new Formula.LatexGroup([F.Id("N")]));
}
