using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class OrdowskiBinomialPowerSumLeastPrimeDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Congruence/OrdowskiBinomialPowerSumLeastPrime.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/ordowski2018a133907");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordowski's binomial and power-sum conditions define the same least prime in OEIS A133907.",
        H("Ordowski's Binomial and Power-Sum Least Prime"),
        Blocks(
            Paragraph(Text("All variables and values lie in the natural numbers N, including zero. "
                + "Here n is the index, p and q are candidate primes, and k is the summation "
                + "index. Prime(p) means that p is "
                + "prime, C(u,v) is the natural binomial coefficient, and a is A133907 as defined "
                + "below. The operator sInf takes the infimum in N, equal to the least element "
                + "of a nonempty set and zero for the empty set. The sum runs over all natural "
                + "k from 1 through n, inclusive; powers and the truncated subtraction p-1 are "
                + "natural-number operations. Congruence modulo p means equality of residues, "
                + "and the order is the natural-number order. For every prime p, both membership "
                + "conditions are equivalent to p dividing floor(n/p): Lucas gives the binomial "
                + "residue, and Fermat together with the count of multiples gives the power-sum "
                + "residue. Here n/p is natural-number division, namely floor(n/p). Only the "
                + "Conjecture sentence of Ordowski's comment is settled; the clause "
                + "'Thus a(n) >= A317358(n)' is a consequence, not claimed separately.")),
            Node("a", "The A133907 sequence", DefinitionFormula(),
                "This is the original NAME definition: the least prime p with C(n+p,p) "
                + "congruent to one modulo p. A prime greater than n satisfies the condition, "
                + "so the defining set is nonempty and its natural infimum is attained. "
                + "The OEIS offset is 1,1; the total Lean definition also exists at zero.",
                DescribeRole.Definition),
            Node("result", "Ordowski's least-prime conjecture", ResultFormula(),
                "For every n > 0, a(n) belongs to the displayed power-sum prime set and is "
                + "at most every element q of that set. This membership-and-minimality "
                + "conjunction renders Lean's IsLeast without dropping either obligation. "
                + "For a prime p, Lucas gives C(n+p,p) congruent to floor(n/p)+1. Fermat "
                + "gives the sum congruent to n-floor(n/p), with subtraction interpreted in "
                + "the residue field ZMod p. Both conditions reduce to p dividing floor(n/p), "
                + "and the natural infimum transfers across their pointwise equivalence. "
                + "All auxiliary facts are local steps inside result; the positive-index "
                + "hypothesis is retained. The unsigned floor-division comment is explanatory "
                + "and receives no separate resolution claim.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a133907-ordowski-binomial-power-sum-least-prime"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a133907-" + name),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Less(Formula left, Formula right) => Seq(left, Sp, Lt, Sp, right);
    private static Formula LessOrEqual(Formula left, Formula right) => Seq(left, Sp, Leq, Sp, right);
    private static Formula Member(Formula value, Formula set) => Seq(value, Sp, InMacro, Sp, set);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula And(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Implication(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Implies, Sp, Parenthesized(right));
    private static Formula Universal(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Congruent(Formula left, Formula right, Formula modulus) =>
        Seq(left, Sp, Equiv, Sp, right, Sp, Parenthesized(Seq(Named("mod"), Sp, modulus)));
    private static Formula PrimeSet(Formula p, Formula condition) =>
        Seq(OpenBrace, p, Sp, InMacro, Sp, Naturals(), Sp, Mid, Sp,
            And(Call("Prime", p), condition), CloseBrace);

    private static Formula PowerSum(Formula n, Formula p)
    {
        var k = F.Id("k");
        return Seq(Sum, Underscore, Grp(k, Sp, Eq, Sp, D(1)), Caret, Grp(n), Sp,
            new Formula.Power(k, Subtract(p, D(1))));
    }

    private static Formula DefinitionFormula()
    {
        var n = F.Id("n");
        var p = F.Id("p");
        var candidates = PrimeSet(p, Congruent(Call("C", Add(n, p), p), D(1), p));
        return Disp(Universal("n", Naturals(), Equal(Call("a", n), Call("sInf", candidates))));
    }

    private static Formula ResultFormula()
    {
        var n = F.Id("n");
        var p = F.Id("p");
        var q = F.Id("q");
        var candidates = PrimeSet(p, Congruent(Parenthesized(PowerSum(n, p)), n, p));
        var value = Call("a", n);
        var least = And(Member(value, candidates),
            Universal("q", candidates, LessOrEqual(value, q)));
        return Disp(Universal("n", Naturals(), Implication(Less(D(0), n), least)));
    }
}
