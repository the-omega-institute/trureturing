using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class KoutschanKrattenthalerSchlosserShiftedGDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserShiftedG.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/koutschan2024determinantevaluations");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The binomial determinant identities follow from a common column multiplier and triangular determinant reductions.",
        H("Koutschan–Krattenthaler–Schlosser: ShiftedG"),
        Blocks(
            Node("binom", "Generalized binomial coefficients", BinomFormula(),
                "Page 1, (1.2): the binomial coefficient is defined by α(α−1)⋯(α−p+1)/p! for p ≥ 0, and 0 for p < 0. Here x is rational and p is an integer; Ring.choose supplies the falling-factorial expression when p is nonnegative.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("G", "The four-parameter determinants", GFormula(),
                "Page 32: “Let us denote” G_{α,β,γ,δ}(n) := det_{0≤i,j≤n−1}(2^{i+β} binom(i+4j+γ,4j+α) + binom(−i+4j+δ,4j+α)). The four parameters are integers. Rows and columns are Fin n, starting at zero; powers of 2 have integer exponents and entries lie in the rationals.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 23, equation (10.12)",
                EqF(Call("claim"), Parenthesized(ClaimBody())),
                "Page 33: “Moreover, the following identities are conjectured to hold for all n ≥ 3:” “G₂,₁,₂,₀(n) = 2 G₇,₄,₇,−₁(n − 1). (10.12)” Natural n encodes the matrix size; every adjacent equality is retained as a conjunct. Subtraction of natural indices is truncated at zero.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The determinant identity", ClaimBody(),
                "The column generating functions are sums of two shifted inverse powers. Multiplication of adjacent column differences by the inverse of (1−X)(1−2X)(1−2X+2X²) preserves each finite determinant. The resulting columns agree after their initial zero blocks, so block determinants and the first-row expansion give the rational factors and size shifts.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("link_BC", "link BC", PublicFormula("link_BC"),
                "The common transformed columns and their vanishing initial block give this determinant ratio. The initial block determinants determine its rational factor.", DescribeRole.Lemma, AssessedProvenance.FromRepo(Source)),
            Node("link_PD", "link PD", PublicFormula("link_PD"),
                "The common transformed columns and their vanishing initial block give this determinant ratio. The initial block determinants determine its rational factor.", DescribeRole.Lemma, AssessedProvenance.FromRepo(Source)),
            Node("link_PE", "link PE", PublicFormula("link_PE"),
                "The common transformed columns and their vanishing initial block give this determinant ratio. The initial block determinants determine its rational factor.", DescribeRole.Lemma, AssessedProvenance.FromRepo(Source)),
            Node("link_TF", "link TF", PublicFormula("link_TF"),
                "The common transformed columns and their vanishing initial block give this determinant ratio. The initial block determinants determine its rational factor.", DescribeRole.Lemma, AssessedProvenance.FromRepo(Source)),
            Node("link_HI", "link HI", PublicFormula("link_HI"),
                "The common transformed columns and their vanishing initial block give this determinant ratio. The initial block determinants determine its rational factor.", DescribeRole.Lemma, AssessedProvenance.FromRepo(Source)),
            Node("link_VJ", "link VJ", PublicFormula("link_VJ"),
                "The common transformed columns and their vanishing initial block give this determinant ratio. The initial block determinants determine its rational factor.", DescribeRole.Lemma, AssessedProvenance.FromRepo(Source)),
            Node("link_VK", "link VK", PublicFormula("link_VK"),
                "The common transformed columns and their vanishing initial block give this determinant ratio. The initial block determinants determine its rational factor.", DescribeRole.Lemma, AssessedProvenance.FromRepo(Source)),
            Node("prop_H", "prop H", PublicFormula("prop_H"),
                "Page 32, Proposition 22: “For all integers n ≥ 2 we have the following relations:” “G₁,₁,₀,−₂(n) = −2 G₅,₂,₅,₁(n − 1), (10.3)” Replacing the source size by n+1 gives the displayed formula; its first-row reduction also covers size one.", DescribeRole.Lemma, AssessedProvenance.FromLiterature(Source)),
            Node("prop_B", "prop B", PublicFormula("prop_B"),
                "Page 32, Proposition 22: “For all integers n ≥ 2 we have the following relations:” “G₀,₁,−₂,−₄(n) = 3 G₄,₂,₃,−₁(n − 1) = 3 G₈,₃,₈,₂(n − 2), (10.2)” Replacing the source size by n+2 gives the displayed formula after two first-row reductions.", DescribeRole.Lemma, AssessedProvenance.FromLiterature(Source)),
            Node("p_shift_all", "p shift all", PublicFormula("p_shift_all"),
                "The common transformed columns and their vanishing initial block give this determinant ratio. The initial block determinants determine its rational factor.", DescribeRole.Lemma, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("kks-shiftedg-" + name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
        Blocks(Paragraph(Text(prose))), role);
    private static Formula I(int value) => value < 0 ? Neg(new Formula.Number(-value)) : new Formula.Number(value);
    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Z() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Q() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
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
    private static Formula Guarded(Formula lhs, Formula rhs) => All("n", N(),
        Seq(new Formula.Relation(I(3), FormulaRelationOperator.LessThanOrEqual, F.Id("n")),
            Sp, Implies, Sp, Parenthesized(EqF(lhs, rhs))));
    private static Formula Cast(Formula x, Formula type) => Parenthesized(Seq(x, Colon, Sp, type));
    private static Formula BinomFormula()
    {
        var x = F.Id("x"); var p = F.Id("p");
        return All("x", Q(), All("p", Z(), EqF(Call("binom", x, p),
            Call("ite", new Formula.Relation(p, FormulaRelationOperator.LessThan, I(0)), I(0),
                new Formula.Apply(Qualified("Ring", "choose"), [x,
                    new Formula.Apply(Qualified("Int", "toNat"), [p])])))));
    }
    private static Formula GFormula()
    {
        var a = F.Id("a"); var b = F.Id("b"); var c = F.Id("c"); var d = F.Id("d");
        var n = F.Id("n"); var i = F.Id("i"); var j = F.Id("j");
        var iq = Cast(Call("val", i), Q()); var jq = Cast(Call("val", j), Q());
        var iz = Cast(Call("val", i), Z()); var jz = Cast(Call("val", j), Z());
        var lower = Add(Mul(I(4), jz), a);
        var entry = Add(Mul(new Formula.Power(Cast(I(2), Q()), Add(iz, b)),
            Call("binom", Add(Add(iq, Mul(I(4), jq)), Cast(c, Q())), lower)),
            Call("binom", Add(Add(Neg(iq), Mul(I(4), jq)), Cast(d, Q())), lower));
        var f = Seq(F.Id("fun"), Sp, i, Sp, j, Colon, Sp, Call("Fin", n), Sp, Mapsto, Sp, entry);
        return All("a", Z(), All("b", Z(), All("c", Z(), All("d", Z(), All("n", N(),
            EqF(Call("G", a, b, c, d, n), new Formula.Apply(Qualified("Matrix", "det"),
                [new Formula.Apply(Qualified("Matrix", "of"), [f])])))))));
    }
    private static Formula LinkFormula(int lower, Formula lhs, Formula rhs) => All("n", N(),
        Seq(new Formula.Relation(I(lower), FormulaRelationOperator.LessThanOrEqual, F.Id("n")),
            Sp, Implies, Sp, Parenthesized(EqF(lhs, rhs))));
    private static Formula PublicFormula(string name)
    {
        var n = F.Id("n");
        return name switch
        {
            "link_BC" => LinkFormula(3, Gi(1, 3, -2, -8, n), Mul(I(-448), Gi(0, 1, -2, -4, n))),
            "link_PD" => LinkFormula(2, Gi(5, 4, 3, -5, n), Mul(I(63), Gi(3, 0, 3, 3, n))),
            "link_PE" => LinkFormula(3, Gi(6, 6, 3, -9, n), Mul(Rat(1002001, 4), Gi(3, 0, 3, 3, n))),
            "link_TF" => LinkFormula(1, Gi(8, 3, 8, 2, n), Mul(Neg(Rat(4, 5)), Gi(9, 5, 8, -2, n))),
            "link_HI" => LinkFormula(2, Gi(1, 1, 0, -2, n), Mul(Neg(Rat(1, 49)), Gi(2, 3, 0, -6, n))),
            "link_VJ" => LinkFormula(1, Gi(5, 2, 5, 1, n), Mul(Rat(1, 7), Gi(6, 4, 5, -3, n))),
            "link_VK" => LinkFormula(2, Gi(5, 2, 5, 1, n), Mul(Rat(2, 5577), Gi(7, 6, 5, -7, n))),
            "prop_H" => All("n", N(), EqF(Gi(1, 1, 0, -2, Add(n, I(1))), Mul(I(-2), Gi(5, 2, 5, 1, n)))),
            "prop_B" => All("n", N(), EqF(Gi(0, 1, -2, -4, Add(n, I(2))), Mul(I(3), Gi(8, 3, 8, 2, n)))),
            "p_shift_all" => All("n", N(), EqF(Gi(3, 0, 3, 3, Add(n, I(1))), Mul(I(2), Gi(8, 3, 8, 2, n)))),
            _ => throw new System.ArgumentException("Unknown determinant relation", nameof(name))
        };
    }
    private static Formula ClaimBody()
    {
        var n = F.Id("n");
        return Guarded(Gi(2, 1, 2, 0, n), Mul(I(2), Gi(7, 4, 7, -1, Sub(n, I(1)))));
    }
}
