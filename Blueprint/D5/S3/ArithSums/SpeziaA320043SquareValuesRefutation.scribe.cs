using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class SpeziaA320043SquareValuesRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithSums/SpeziaA320043SquareValuesRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/spezia2018a320043");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A prime row and the Pell equation give an additional square value of OEIS A320043.",
        H("Spezia's A320043 square-value conjecture is false"),
        Blocks(
            Node("a", "The gcd-weighted row sum", SequenceFormula(),
                "OEIS A320043, revision 43, first FORMULA (unpaginated): "
                    + "\"a(n) = Sum_{k=1..n} (n + 1 - k)^2*k/gcd(n + 1 - k, k)^3.\" "
                    + "Here n and k are natural numbers. Nat.div is natural-number division, "
                    + "and subtraction is natural subtraction. For 1 <= k <= n, both gcd "
                    + "arguments are positive and the denominator divides the numerator "
                    + "exactly. The value at n = 0 is the empty sum; the source starts at n = 1.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The source conjecture", Disp(Equal(F.Id("claim"), ClaimBody())),
                "OEIS A320043, revision 43, sole COMMENTS conjecture (unpaginated): "
                    + "\"Conjecture: a(n) is not a perfect square except for n = 1, 6 and 96.\" "
                    + "The positive index n and the square root m range over natural numbers. "
                    + "The OFFSET field is 1,2; its first entry supplies the positive-index domain.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "An additional square refutes the conjecture",
                Disp(new Formula.Not(Parenthesized(ClaimBody()))),
                "Take p = 708158977 and y = 204427888. Lucas's criterion proves p prime, "
                    + "and p squared minus 12 times y squared equals 1. For prime p, "
                    + "gcd(p-k,k) equals 1 on 1 <= k < p. A polynomial telescope gives "
                    + "12*a(p-1) = p squared times (p squared minus 1), so the Pell "
                    + "equation gives a(p-1) = (p*y) squared. Thus a(708158976) equals "
                    + "144767444036350576 squared. This positive index differs from 1, 6 and 96. "
                    + "Minimality, infinitely many prime Pell inputs, and classification of "
                    + "other square values remain open.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("a320043-square-values-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("a320043-" + name), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula SequenceFormula()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var u = Subtract(Add(n, D(1)), k);
        var numerator = Multiply(Power(Parenthesized(u), 2), k);
        var denominator = Power(QualifiedCall("Nat", "gcd", u, k), 3);
        var term = QualifiedCall("Nat", "div", numerator, denominator);
        var sum = Seq(new Formula.Subscript(F.Sum,
            Seq(k, Sp, InMacro, Sp, QualifiedCall("Finset", "Icc", D(1), n))), Sp, term);
        return Disp(All("n", Equal(Call("a", n), sum)));
    }

    private static Formula ClaimBody()
    {
        var n = F.Id("n");
        var m = F.Id("m");
        var alternatives = Or(Equal(n, D(1)), Or(Equal(n, D(6)), Equal(n, D(9, 6))));
        return All("n", Implies(LessEqual(D(1), n),
            All("m", Implies(Equal(Call("a", n), Power(m, 2)), alternatives))));
    }

    private static Formula All(string name, Formula body) => new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create(name),
        Seq(Mathbb, Grp(F.Id("N"))), body);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula QualifiedCall(string owner, string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(owner)), Dot,
            Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula Power(Formula body, byte exponent) => new Formula.Power(body, D(exponent));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Subtract(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Multiply(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LessEqual(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(
        Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(
        Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
}
