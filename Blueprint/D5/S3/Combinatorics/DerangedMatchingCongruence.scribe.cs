using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class DerangedMatchingCongruenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/DerangedMatchingCongruence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/richman2023a053871");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For the deranged-matching numbers a(n), which are also the central moments of the chi-squared distribution with one degree of freedom, the signed values (-1)^n a(n) are periodic with period q modulo every odd q.",
        H("Richman's congruence for A053871"),
        Blocks(
            Node("sequence", "The sequence A053871", SequenceFormula(),
                "a(0) = 1, a(1) = 0 and a(n + 2) = 2(n + 1)(a(n + 1) + a(n)); a(n) counts the ways to re-pair n couples so that nobody is paired with the original partner.",
                "a", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Richman's conjecture", ClaimFormula(),
                "For every odd q and all m and n that are congruent modulo q, (-1)^m a(m) and (-1)^n a(n) are congruent modulo q.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Proof of the conjecture", Disp(F.Id("claim")),
                "Put b(n) = (-1)^n a(n); the recurrence becomes b(n + 2) = 2(n + 1)(b(n) - b(n + 1)). The alternating sums c(n) of (-1)^k C(n, k) (2k - 1)!! and d(n) of (-1)^k C(n, k) (2k + 1)!! satisfy c(n + 1) = c(n) - d(n) by Pascal's rule and d(n + 1) = c(n + 1) - 2(n + 1) d(n) because (2k + 1)!! = (2k + 1)(2k - 1)!! and k C(n + 1, k) = (n + 1) C(n, k - 1); together they give the same recurrence for c, and c(0) = 1, c(1) = 0, so b = c. For odd q and k at least 1, 2^k C(q, k) (2k - 1)!! equals q(q - 1)...(q - k + 1) C(2k, k), which is divisible by q, and 2 is invertible modulo q, so every term of c(q) past the first is divisible by q and b(q) is 1 = b(0) modulo q. The recurrence gives b(q + 1) = 2q(b(q - 1) - b(q)), which is 0 = b(1) modulo q. Since the coefficient 2(n + 1) has period q modulo q, induction gives b(n + q) congruent to b(n) for every n, and hence the claim.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("richman-2023-a053871-signed-congruence"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("richman-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Times(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Signed(Formula index) =>
        Times(new Formula.Power(Parenthesized(new Formula.Negate(D(1))), index), Call("a", index));
    private static Formula Congruent(Formula left, Formula right, Formula modulus) =>
        Seq(left, Sp, Equiv, Sp, right, Sp, Parenthesized(Seq(Mathrm, Grp(F.Id("mod")), Sp, modulus)));

    private static Formula SequenceFormula()
    {
        Formula n = F.Id("n");
        Formula recurrence = Equal(Call("a", Add(n, D(2))),
            Times(Times(D(2), Parenthesized(Add(n, D(1)))), Parenthesized(Add(Call("a", Add(n, D(1))), Call("a", n)))));
        return Disp(Seq(Equal(Call("a", D(0)), D(1)), Comma, Quad, Equal(Call("a", D(1)), D(0)), Comma, Quad, recurrence));
    }

    private static Formula ClaimFormula()
    {
        Formula q = F.Id("q"), m = F.Id("m"), n = F.Id("n");
        Formula body = All("q", Naturals(), All("m", Naturals(), All("n", Naturals(), Implies(
            And(Call("Odd", q), Congruent(m, n, q)), Congruent(Signed(m), Signed(n), q)))));
        return Disp(Iff(F.Id("claim"), body));
    }
}
