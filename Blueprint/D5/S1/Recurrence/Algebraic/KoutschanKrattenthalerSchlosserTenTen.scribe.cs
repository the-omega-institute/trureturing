using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class KoutschanKrattenthalerSchlosserTenTenDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserTenTen.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/koutschan2024determinantevaluations");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The binomial determinant identities follow from a common column multiplier and triangular determinant reductions.",
        H("Koutschan–Krattenthaler–Schlosser: TenTen"),
        Blocks(
            Node("claim", "Conjecture 23, equation (10.10)",
                EqF(Call("claim"), Parenthesized(ClaimBody())),
                "Page 33: “Moreover, the following identities are conjectured to hold for all n ≥ 3:” “G₃,₀,₃,₃(n) = ⅔ G₀,₁,−₂,−₄(n + 1) = −(1/672) G₁,₃,−₂,−₈(n + 1) = (1/63) G₅,₄,₃,−₅(n) = (4/1002001) G₆,₆,₃,−₉(n) = −(8/5) G₉,₅,₈,−₂(n − 1). (10.10)” Natural n encodes the matrix size; every adjacent equality is retained as a conjunct. Subtraction of natural indices is truncated at zero.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The determinant identity", ClaimBody(),
                "The column generating functions are sums of two shifted inverse powers. Multiplication of adjacent column differences by the inverse of (1−X)(1−2X)(1−2X+2X²) preserves each finite determinant. The resulting columns agree after their initial zero blocks, so block determinants and the first-row expansion give the rational factors and size shifts.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("koutschan-krattenthaler-schlosser-2024-ten-ten-determinants"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("kks-tenten-" + name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
        Blocks(Paragraph(Text(prose))), role, resolution);
    private static Formula I(int value) => value < 0 ? Neg(new Formula.Number(-value)) : new Formula.Number(value);
    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula EqF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Neg(Formula a) => new Formula.Negate(a);
    private static Formula Rat(int a, int b) => new Formula.Fraction(I(a), I(b));
    private static Formula Gi(int a, int b, int c, int d, Formula n) =>
        Call("G", I(a), I(b), I(c), I(d), n);
    private static Formula ClaimBody()
    {
        var n = F.Id("n");
        var a = Gi(3, 0, 3, 3, n);
        var b = Mul(Rat(2, 3), Gi(0, 1, -2, -4, Add(n, I(1))));
        var c = Mul(Neg(Rat(1, 672)), Gi(1, 3, -2, -8, Add(n, I(1))));
        var d = Mul(Rat(1, 63), Gi(5, 4, 3, -5, n));
        var e = Mul(Rat(4, 1002001), Gi(6, 6, 3, -9, n));
        var f = Mul(Neg(Rat(8, 5)), Gi(9, 5, 8, -2, Sub(n, I(1))));
        return All("n", N(), Seq(new Formula.Relation(I(3), FormulaRelationOperator.LessThanOrEqual, n),
            Sp, Implies, Sp, Parenthesized(Seq(Parenthesized(EqF(a, b)), Sp, Land, Sp,
                Parenthesized(EqF(b, c)), Sp, Land, Sp, Parenthesized(EqF(c, d)), Sp, Land, Sp,
                Parenthesized(EqF(d, e)), Sp, Land, Sp, Parenthesized(EqF(e, f))))));
    }
}
