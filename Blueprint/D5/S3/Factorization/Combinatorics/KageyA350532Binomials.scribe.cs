using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Combinatorics;

internal sealed class KageyA350532BinomialsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/Combinatorics/KageyA350532Binomials.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/kagey2022a350532");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact GF(2) sparse perfect-power counts.",
        H("Binomial perfect powers over GF(2)"),
        Blocks(
            Describe.Lean(DescribeId.Create("kagey350532-count"),
                DeclarationHandle.Create(Prefix + "T"), H("The sparse proper-power count"),
                StatementSource.FromAuthor(Disp(CountDefinition())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "OEIS A350532, unpaginated NAME: \"Triangle read by rows: T(n,k) is the number of degree-n polynomials over Z/2Z of the form f(x)^m for some m > 1 with exactly k nonzero terms; 1 <= k <= n + 1.\" "
                    + "Here n and k are natural numbers, Polynomial (ZMod 2) is the polynomial ring, and Nat.card counts distinct nonzero polynomials rather than representations as powers. "
                    + "The displayed expression also defines T outside the triangular range."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("kagey350532-binomial-claim"),
                DeclarationHandle.Create(Prefix + "claim"), H("Kagey's binomial conjecture"),
                StatementSource.FromAuthor(Disp(Equal(I("claim"), Parenthesized(ClaimBody())))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "OEIS A350532, unpaginated COMMENT: \"Conjecture: T(2*n,2) = n.\" "
                    + "The variable n ranges over all natural numbers, including zero."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("kagey350532-shared-count"),
                DeclarationHandle.Create(Prefix + "card_sparse_powers"), H("Two- and three-term counts"),
                StatementSource.FromAuthor(Disp(SharedCount())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "A proper power with two or three nonzero terms has an even exponent. "
                    + "After removing the maximal power of X, the derivative and descent under exponent contraction rule out odd proper powers. "
                    + "Squaring doubles every exponent and preserves support size, so contraction identifies the counted polynomials with degree-n polynomials having k+1 terms. "
                    + "Erasing the leading exponent identifies their supports with k-element subsets of Finset.range n. "
                    + "This count also holds when n is zero."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("kagey350532-binomial-result"),
                DeclarationHandle.Create(Prefix + "result"), H("The binomial count"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The two-term case has exactly n possibilities in degree 2*n. "
                    + "Each is the square of a degree-n polynomial with two terms; the lower exponent can be any natural number strictly below n."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kagey350532-perfectpowers"), ResolutionKind.Proved)))));

    private static Formula CountDefinition()
    {
        var p = I("p");
        var predicate = And(NotEqual(p, D(0)),
            And(Equal(App(Q("Polynomial", "natDegree"), p), I("n")),
                And(Equal(App(Q("Finset", "card"), App(Q("Polynomial", "support"), p)), I("k")),
                    ExistsTyped("f", PolynomialType(), ExistsTyped("m", NatType(),
                        And(Less(D(1), I("m")), Equal(p, Power(I("f"), I("m")))))))));
        var subtype = Seq(OpenBrace, p, Colon, Sp, PolynomialType(), Sp, Slash, Slash, Sp,
            predicate, CloseBrace);
        return All("n", NatType(), All("k", NatType(),
            Equal(Call("T", I("n"), I("k")), App(Q("Nat", "card"), subtype))));
    }

    private static Formula ClaimBody() => All("n", NatType(),
        Equal(Call("T", Multiply(D(2), I("n")), D(2)), I("n")));

    private static Formula SharedCount() => All("n", NatType(), All("k", NatType(),
        Implies(LessEqual(D(1), I("k")), Implies(LessEqual(I("k"), D(2)),
            Equal(Call("T", Multiply(D(2), I("n")), Add(I("k"), D(1))),
                App(Q("Nat", "choose"), I("n"), I("k")))))));

    private static Formula I(string name) => F.Id(name);
    private static Formula Q(string owner, string name) =>
        Seq(Operatorname, Grp(I(owner)), Dot, Operatorname, Grp(I(name)));
    private static Formula App(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);
    private static Formula NatType() => I("Nat");
    private static Formula PolynomialType() => Call("Polynomial", Call("ZMod", D(2)));
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(I(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula ExistsTyped(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(I(name), Colon, Sp, type)), Comma, Sp, body);
}
