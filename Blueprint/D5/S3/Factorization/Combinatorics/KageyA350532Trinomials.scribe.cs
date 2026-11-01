using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Combinatorics;

internal sealed class KageyA350532TrinomialsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/Combinatorics/KageyA350532Trinomials.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/kagey2022a350532");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact GF(2) trinomial perfect-power counts.",
        H("Trinomial perfect powers over GF(2)"),
        Blocks(
            Describe.Lean(DescribeId.Create("kagey350532-trinomial-claim"),
                DeclarationHandle.Create(Prefix + "claim"), H("Kagey's trinomial conjecture"),
                StatementSource.FromAuthor(Disp(Equal(I("claim"), Parenthesized(ClaimBody())))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "OEIS A350532, unpaginated COMMENT: \"Conjecture: T(2*n,3) = (n^2 - n)/2 for n >= 1.\" "
                    + "The variable n is a natural number. Both subtraction and Nat.div are natural-number operations, with Nat.div denoting integer division. "
                    + "KageyA350532Binomials.T counts distinct nonzero polynomials over ZMod 2."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("kagey350532-trinomial-result"),
                DeclarationHandle.Create(Prefix + "result"), H("The trinomial count"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Squaring gives a bijection with degree-n trinomials. "
                    + "Their two lower exponents form a two-element subset of Finset.range n, giving Nat.choose n 2. "
                    + "The binomial-coefficient identity gives the stated natural-number quotient."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kagey350532-trinomials"), ResolutionKind.Proved)))));

    private static Formula ClaimBody()
    {
        var n = I("n");
        var count = App(Q("KageyA350532Binomials", "T"), Multiply(D(2), n), D(3));
        var quotient = App(Q("Nat", "div"), Parenthesized(Subtract(new Formula.Power(n, D(2)), n)), D(2));
        return Seq(Forall, Sp, Parenthesized(Seq(n, Colon, Sp, I("Nat"))), Comma, Sp,
            new Formula.Logic(Parenthesized(new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, n)),
                FormulaLogicOperator.Implies, Parenthesized(Equal(count, quotient))));
    }

    private static Formula I(string name) => F.Id(name);
    private static Formula Q(string owner, string name) =>
        Seq(Operatorname, Grp(I(owner)), Dot, Operatorname, Grp(I(name)));
    private static Formula App(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
}
