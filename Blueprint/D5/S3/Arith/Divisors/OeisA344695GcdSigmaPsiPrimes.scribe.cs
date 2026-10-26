using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors;

internal sealed class OeisA344695GcdSigmaPsiPrimesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Divisors/OeisA344695GcdSigmaPsiPrimes.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/karttunenmunn2021a344695");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The prime values of gcd of the divisor sum and Dedekind psi are the odd primes.",
        H("The Karttunen–Munn conjecture on OEIS A344695"),
        Blocks(
            Node("psi", "Dedekind psi", PsiFormula(),
                "OEIS A001615, NAME (unpaginated): \"Dedekind psi function: n * Product_{p|n, p prime} (1 + 1/p).\" "
                + "Here n is natural and Nat.primeFactors n is the finite set of distinct prime divisors. "
                + "Nat.div denotes natural-number integer division, with empty products equal to one. For positive n "
                + "the product of the prime divisors divides n, giving the displayed integer expression.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a", "The sequence", AFormula(),
                "OEIS A344695, NAME (revision 39, unpaginated): \"a(n) = gcd(sigma(n), psi(n)), where sigma is the sum of divisors function, A000203, and psi is the Dedekind psi function, A001615.\" "
                + "ArithmeticFunction.sigma 1 n is the sum of positive divisors of n. "
                + "The sequence uses the positive indices n ≥ 1.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The prime-values conjecture", ClaimFormula(),
                "OEIS A344695, COMMENTS (revision 39, unpaginated): \"Conjecture: the set of primes that appear in the sequence is A065091 (the odd primes).\" "
                + "For each natural prime q, appearing means that some natural n ≥ 1 satisfies a n = q. "
                + "Odd is the natural-number parity predicate.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The prime values are exactly the odd primes", Disp(ClaimBody()),
                "For a square index, the divisor sum is odd. For a nonsquare index, a prime p "
                + "of odd exponent makes p + 1 divide both functions, excluding the value 2. "
                + "For an odd prime q, choose a prime r greater than q² + q + 1 and congruent "
                + "to 1 modulo q(q + 1)(q² + q + 1). At n = q²r^(q−1), geometric-sum "
                + "congruences and coprimality give a n = q.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a344695-gcd-sigma-psi-odd-primes"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("a344695-" + name),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role,
            openProblemResolutionClaim: resolution);

    private static Formula PsiFormula()
    {
        var n = F.Id("n");
        var p = F.Id("p");
        var radical = PrimeProduct(n, p);
        var shifted = PrimeProduct(n, new Formula.Binary(p, FormulaBinaryOperator.Add, D(1)));
        var quotient = new Formula.Apply(Qualified("Nat", "div"), [n, radical]);
        return Disp(All("n", Equal(Call("psi", n),
            new Formula.Binary(Parenthesized(quotient), FormulaBinaryOperator.Multiply,
                Parenthesized(shifted)))));
    }

    private static Formula AFormula()
    {
        var n = F.Id("n");
        return Disp(All("n", Equal(Call("a", n),
            new Formula.Apply(Qualified("Nat", "gcd"),
                [new Formula.Apply(Qualified("ArithmeticFunction", "sigma"), [D(1), n]),
                    Call("psi", n)]))));
    }

    private static Formula ClaimFormula() => Disp(Seq(F.Id("claim"), Sp, Colon, Eq, Sp,
        Parenthesized(ClaimBody())));

    private static Formula ClaimBody()
    {
        var n = F.Id("n");
        var q = F.Id("q");
        var positive = new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, n);
        var occurs = new Formula.Bind(FormulaQuantifier.Exists,
            FormulaIdentifier.Create("n"), Naturals(),
            new Formula.Logic(Parenthesized(positive), FormulaLogicOperator.And,
                Parenthesized(Equal(Call("a", n), q))));
        var equivalence = new Formula.Logic(Parenthesized(occurs), FormulaLogicOperator.Iff,
            Parenthesized(Call("Odd", q)));
        return All("q", new Formula.Logic(new Formula.Apply(Qualified("Nat", "Prime"), [q]),
            FormulaLogicOperator.Implies, Parenthesized(equivalence)));
    }

    private static Formula PrimeProduct(Formula n, Formula term) =>
        Seq(new Formula.Subscript(Prod, Seq(F.Id("p"), Sp, InMacro, Sp,
            new Formula.Apply(Qualified("Nat", "primeFactors"), [n]))), Sp, Parenthesized(term));

    private static Formula All(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), Naturals(), body);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
}
