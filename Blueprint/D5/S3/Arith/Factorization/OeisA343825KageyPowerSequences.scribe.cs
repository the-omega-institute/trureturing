using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Factorization;

internal sealed class OeisA343825KageyPowerSequencesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Factorization/OeisA343825KageyPowerSequences.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/kagey2021a343825");
    private const string SequenceQuote =
        "Table read by antidiagonals upward: T(n,k) is the least m such that there exists a sequence "
        + "k = b_1 <= b_2 <= ... <= b_t = m such that no term appears n or more times and the product "
        + "of the sequence is of the form c^n, where c is an integer; n >= 1 and k >= 0.";
    private const string RelationQuote =
        "Least integer m >= n such that there exist integers k_n, k_n+1, ..., k_m with nonzero k_n, "
        + "for which n^(k_n) * (n+1)^(k_n+1) * ... * m^(k_m) = 1.";
    private const string ConjectureQuote =
        "Conjecture: T(p,k) = A071537(k) for fixed k and sufficiently large prime p.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime-power sequence minima eventually equal the rational-relation minimum.",
        H("Kagey's Eventual Equality of Power-Sequence Minima"), Blocks(
            Node("Valid", "Admissible nondecreasing sequences", ValidFormula(),
                SequenceQuote + " (OEIS A343825, NAME, revision 22; unpaginated.) "
                + "The sequence is a list of natural numbers. Optional heads and last elements below "
                + "are written headOption and lastOption; they denote `List.head?` and `List.getLast?`. "
                + "Pairwise uses the natural order. The count "
                + "of each member is strictly below n, and the natural product, cast to the integers, "
                + "is an integer nth power.", AssessedProvenance.FromLiterature(Source)),
            Node("T", "The least power-sequence endpoint", TFormula(),
                SequenceQuote + " (OEIS A343825, NAME, revision 22; unpaginated.) "
                + "Nat.find selects the least natural endpoint with an admissible sequence. "
                + "The value is extended by zero if there is no endpoint.",
                AssessedProvenance.FromLiterature(Source)),
            Node("Relation", "An integer-exponent relation", RelationFormula(),
                RelationQuote + " (OEIS A071537, NAME; unpaginated.) "
                + "The source's starting index n is written k. Exponents are integers; the finite "
                + "product is taken in the rationals over the closed natural interval from k to m. "
                + "The first exponent must be nonzero.", AssessedProvenance.FromLiterature(Source)),
            Node("A071537", "The least relation endpoint", MinimumFormula(),
                RelationQuote + " (OEIS A071537, NAME; unpaginated.) "
                + "Nat.find selects the least m at least k carrying such a relation. The value is "
                + "extended by zero if there is no endpoint. A071537 has offset one.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The eventual-equality conjecture",
                Disp(Iff(F.Id("claim"), Parenthesized(ClaimBody()))),
                ConjectureQuote + " (OEIS A343825, COMMENT, revision 22; unpaginated.) "
                + "For each natural k at least one, a threshold N works for every prime p at least N.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(DescribeId.Create("kagey-power-result"),
                DeclarationHandle.Create(Prefix + "result"), H("Equality for all sufficiently large primes"),
                StatementSource.FromAuthor(Disp(ClaimBody())), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Fix k at least one and let m be its least rational-relation endpoint. Such an "
                    + "endpoint exists because the factorization vector of k times k+1 is the sum "
                    + "of the two factorization vectors. Reducing relation exponents modulo a "
                    + "sufficiently large prime gives multiplicities below that prime and a positive "
                    + "multiplicity at k. Sorting the replicated entries gives an admissible list "
                    + "whose endpoint is at most m. A rational prime-power root of a natural number "
                    + "has denominator one, so the root is an integer.")),
                    Paragraph(Text(
                    "For each earlier endpoint, rational linear separation supplies an integer "
                    + "functional that vanishes at all later factorization vectors and is nonzero "
                    + "at k. A prime larger than the absolute value of its value at k cannot divide that value. "
                    + "Prime divisibility would therefore force the positive multiplicity at k "
                    + "to be at least the prime, a contradiction. The maximum of these finitely "
                    + "many thresholds and the upper threshold proves the equality, including k=1. "
                    + "The argument leaves an explicit threshold, a characterization of exceptional "
                    + "primes, and the separate prime-row permutation assertion open."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a343825-kagey-power-sequences"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("kagey-power-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula ValidFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k"), m = F.Id("m"), b = F.Id("b");
        Formula x = F.Id("x"), c = F.Id("c");
        Formula ordered = App(Q("List", "Pairwise"),
            Parenthesized(Seq(Keyword("fun"), Sp, F.Id("a"), Sp, F.Id("d"), Sp,
                Mapsto, Sp, LeqF(F.Id("a"), F.Id("d")))), b);
        Formula countBound = All("x", Nat(), Imply(Member(x, b),
            Less(App(Q("List", "count"), x, b), n)));
        Formula integerPower = Some("c", new Formula.Integers(),
            Equal(Typed(App(Q("List", "prod"), b), new Formula.Integers()),
                new Formula.Power(c, n)));
        Formula body = And(Equal(Call("headOption", b), Call("some", k)),
            And(Equal(Call("lastOption", b), Call("some", m)),
                And(ordered, And(countBound, integerPower))));
        return Disp(All("n", Nat(), All("k", Nat(), All("m", Nat(), All("b", Call("List", Nat()),
            Iff(Call("Valid", n, k, m, b), Parenthesized(body)))))));
    }

    private static Formula TFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k"), m = F.Id("m"), b = F.Id("b");
        Formula exists = Some("m", Nat(), Some("b", Call("List", Nat()), Call("Valid", n, k, m, b)));
        return Disp(All("n", Nat(), All("k", Nat(), Equal(Call("T", n, k), FindOrZero(exists)))));
    }

    private static Formula RelationFormula()
    {
        Formula k = F.Id("k"), m = F.Id("m"), e = F.Id("e"), j = F.Id("j");
        Formula product = Seq(new Formula.Subscript(Prod,
            Seq(j, Sp, InMacro, Sp, App(Q("Finset", "Icc"), k, m))), Sp,
            new Formula.Power(Parenthesized(Typed(j, Rat())), App(e, j)));
        Formula body = Some("e", new Formula.TypeArrow(Nat(), new Formula.Integers()),
            And(new Formula.Relation(App(e, k), FormulaRelationOperator.NotEqual, D(0)), Equal(product, D(1))));
        return Disp(All("k", Nat(), All("m", Nat(),
            Iff(Call("Relation", k, m), Parenthesized(body)))));
    }

    private static Formula MinimumFormula()
    {
        Formula k = F.Id("k"), m = F.Id("m");
        Formula exists = Some("m", Nat(), And(LeqF(k, m), Call("Relation", k, m)));
        return Disp(All("k", Nat(), Equal(Call("A071537", k), FindOrZero(exists))));
    }

    private static Formula FindOrZero(Formula exists) => Parenthesized(Seq(Keyword("if"), Sp,
        F.Id("h"), Sp, Colon, Sp, Parenthesized(exists), Sp, Keyword("then"), Sp,
        App(Q("Nat", "find"), F.Id("h")), Sp, Keyword("else"), Sp, D(0)));

    private static Formula ClaimBody()
    {
        Formula k = F.Id("k"), n = F.Id("N"), p = F.Id("p");
        return All("k", Nat(), Imply(LeqF(D(1), k), Some("N", Nat(), All("p", Nat(),
            Imply(App(Q("Nat", "Prime"), p), Imply(LeqF(n, p),
                Equal(Call("T", p, k), Call("A071537", k))))))));
    }

    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Rat() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Keyword(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Q(string owner, string name) => Seq(Keyword(owner), Dot, Keyword(name));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(F.Id(name), args);
    private static Formula Typed(Formula value, Formula type) => Seq(Parenthesized(value), Sp, Colon, Sp, type);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Some(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LeqF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imply(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
