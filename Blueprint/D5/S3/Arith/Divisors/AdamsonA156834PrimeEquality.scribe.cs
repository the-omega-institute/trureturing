using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors;

internal sealed class AdamsonA156834PrimeEqualityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Divisors/AdamsonA156834PrimeEquality.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/elabdalaouidahmouneziadi2013automata");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adamson's A156834 equals its index exactly at primes greater than one.",
        H("Adamson's OEIS A156834 prime-equality conjecture"),
        Blocks(
            Node("a", "The totient-weighted divisor sum", AFormula(),
                "OEIS A156834, FORMULA (revision 20, unpaginated), states: "
                + "\"a(n) = Sum_{d|n} phi(d) * binomial(d+n/d-2, d-1).\" "
                + "The formula is due to Seiichi Manyama. Here n and d are natural numbers; "
                + "Nat.divisors n contains the positive divisors, Nat.totient is Euler's totient "
                + "with Nat.totient 1 = 1, and Nat.choose is the ordinary binomial coefficient. "
                + "Nat.div is natural-number integer division and subtraction in this formula "
                + "is natural subtraction. For a positive divisor d, both d and n / d are positive. "
                + "The binomial factor is the entry in row n and column d of the "
                + "Eratosthenes-Pascal triangle in el Abdalaoui–Dahmoune–Ziadi, "
                + "arXiv:1301.3751v1, §5.2, Proposition 6, p. 11. The sequence starts at n = 1; "
                + "the total function's value at zero is outside the assertion.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Adamson's prime-equality assertion",
                Disp(Equal(F.Id("claim"), Parenthesized(ClaimBody()))),
                "OEIS A156834, COMMENTS (revision 20, unpaginated), states verbatim: "
                + "\"Conjecture: for n>1, a(n) = n iff n is prime. Companion to A156833.\" "
                + "The variable n ranges over Nat, the antecedent is 1 < n, and primality "
                + "is Nat.Prime n. Both directions of the equivalence are asserted.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Equality characterizes prime indices", Disp(ClaimBody()),
                "Subtracting Nat.sum_totient from the defining sum expresses the integer "
                + "difference a n − n as a sum of products of Nat.totient d with the binomial "
                + "coefficient's excess over one. Nat.choose_pos and Nat.choose_eq_one_iff show that these terms "
                + "are nonnegative, and vanish exactly at the divisor endpoints d = 1 and d = n. "
                + "For prime n, every divisor is an endpoint. For composite n > 1, a proper "
                + "divisor has a strictly positive contribution, so n < a n. Thus the weighted "
                + "sequence has the claimed equality precisely at prime indices. The companion "
                + "A156833 assertion is a separate question.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("adamson-a156834"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("a156834-" + name),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role,
            openProblemResolutionClaim: resolution);

    private static Formula AFormula()
    {
        var n = F.Id("n");
        var d = F.Id("d");
        var upper = new Formula.Binary(
            new Formula.Binary(d, FormulaBinaryOperator.Add, App(Qualified("Nat", "div"), n, d)),
            FormulaBinaryOperator.Subtract, D(2));
        var lower = new Formula.Binary(d, FormulaBinaryOperator.Subtract, D(1));
        var term = new Formula.Binary(App(Qualified("Nat", "totient"), d),
            FormulaBinaryOperator.Multiply, App(Qualified("Nat", "choose"), upper, lower));
        var sum = Seq(new Formula.Subscript(Sum,
            Seq(d, Sp, InMacro, Sp, App(Qualified("Nat", "divisors"), n))), Sp, Parenthesized(term));
        return Disp(All("n", Equal(App(F.Id("a"), n), sum)));
    }

    private static Formula ClaimBody()
    {
        var n = F.Id("n");
        var condition = new Formula.Relation(D(1), FormulaRelationOperator.LessThan, n);
        var equivalence = new Formula.Logic(Parenthesized(Equal(App(F.Id("a"), n), n)),
            FormulaLogicOperator.Iff, Parenthesized(App(Qualified("Nat", "Prime"), n)));
        return All("n", new Formula.Logic(Parenthesized(condition),
            FormulaLogicOperator.Implies, Parenthesized(equivalence)));
    }

    private static Formula All(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name),
            new Formula.NamedConstant(FormulaIdentifier.Create("Nat")), body);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
