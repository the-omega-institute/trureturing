using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class KoutschanKrattenthalerSchlosserTenElevenDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserTenEleven.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/koutschan2024determinantevaluations");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The binomial determinant identities follow from a common column multiplier and triangular determinant reductions.",
        H("Koutschan–Krattenthaler–Schlosser: TenEleven"),
        Blocks(
            Node("claim", "Conjecture 23, equation (10.11)",
                EqF(Call("claim"), Parenthesized(ClaimBody())),
                "Page 33: “Moreover, the following identities are conjectured to hold for all n ≥ 3:” “G₁,₁,₀,−₂(n) = −(1/49) G₂,₃,₀,−₆(n) = −(2/7) G₆,₄,₅,−₃(n − 1) = −(4/5577) G₇,₆,₅,−₇(n − 1). (10.11)” Natural n encodes the matrix size; every adjacent equality is retained as a conjunct. Subtraction of natural indices is truncated at zero.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The determinant identity", ClaimBody(),
                "The column generating functions are sums of two shifted inverse powers. Multiplication of adjacent column differences by the inverse of (1−X)(1−2X)(1−2X+2X²) preserves each finite determinant. The resulting columns agree after their initial zero blocks, so block determinants and the first-row expansion give the rational factors and size shifts.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("kks-teneleven-" + name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
        Blocks(Paragraph(Text(prose))), role);
    private static Formula I(int value) => value < 0 ? Neg(new Formula.Number(-value)) : new Formula.Number(value);
    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula EqF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Neg(Formula a) => new Formula.Negate(a);
    private static Formula Rat(int a, int b) => new Formula.Fraction(I(a), I(b));
    private static Formula Gi(int a, int b, int c, int d, Formula n) =>
        Call("G", I(a), I(b), I(c), I(d), n);
    private static Formula ClaimBody()
    {
        var n = F.Id("n");
        var a = Gi(1, 1, 0, -2, n);
        var b = Mul(Neg(Rat(1, 49)), Gi(2, 3, 0, -6, n));
        var c = Mul(Neg(Rat(2, 7)), Gi(6, 4, 5, -3, Sub(n, I(1))));
        var d = Mul(Neg(Rat(4, 5577)), Gi(7, 6, 5, -7, Sub(n, I(1))));
        return All("n", N(), Seq(new Formula.Relation(I(3), FormulaRelationOperator.LessThanOrEqual, n),
            Sp, Implies, Sp, Parenthesized(Seq(Parenthesized(EqF(a, b)), Sp, Land, Sp,
                Parenthesized(EqF(b, c)), Sp, Land, Sp, Parenthesized(EqF(c, d))))));
    }
}
