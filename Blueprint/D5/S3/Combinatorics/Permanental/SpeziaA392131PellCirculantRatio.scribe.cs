using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permanental;

internal sealed class SpeziaA392131PellCirculantRatioDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permanental/SpeziaA392131PellCirculantRatio.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/spezia2026pellcirculant");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The permanent divided by the signed determinant of the Pell circulant tends to one.",
        H("Pell circulant permanent and determinant"),
        Blocks(
            Node("C", "The Pell circulant", MatrixFormula(),
                "OEIS A392131, COMMENT (unpaginated): “a(n) is the determinant of the n X n Toeplitz matrix whose first column is formed by the vector(A000129(n-1), A000129(n-2), ..., A000129(0)) and whose first row is obtained by rotating once the vector (A000129(0), A000129(1), ..., A000129(n-1)) right.” The Pell sequence is D5.S1.Recurrence.PellCompanionGcd.P. Mathlib Matrix.circulant evaluates its vector at i-j, where subtraction is in Fin n. Subtraction in the argument of P is natural-number subtraction, truncated at zero. Nat.cast has target ℝ. Thus the first row is (P(n-1), P(0), ..., P(n-2)); at n=4 it is (5,0,1,2).",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("A392131", "The signed determinant", SequenceFormula("A392131", "det"),
                "OEIS A392131, NAME (unpaginated): “a(n) is the determinant of the n X n circulant matrix whose rows are formed by successively rotating the vector (A000129(0), A000129(1), ..., A000129(n-1)) right.” The COMMENT and four-by-four EXAMPLE specify the initial right rotation used in C. The determinant is signed; the empty determinant is one.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("A392132", "The permanent", SequenceFormula("A392132", "permanent"),
                "OEIS A392132, NAME (unpaginated): “a(n) is the permanent of the n X n circulant matrix whose rows are formed by successively rotating the vector (A000129(0), A000129(1), ..., A000129(n-1)) right.” This uses the same C as A392131, and the empty permanent is one.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The ratio limit", Disp(Equal(F.Id("claim"), ClaimBody())),
                "OEIS A392131, FORMULA (unpaginated): “Conjecture: lim_{n->oo} A392132(n)/a(n) = 1.” OEIS A392132, FORMULA (unpaginated): “Conjecture: lim_{n->oo} a(n)/A392131(n) = 1.” Here a(n) denotes the determinant in A392131 and the permanent in A392132. The formula states the epsilon-N meaning of that limit over the tail n≥2, with the signed determinant in the denominator.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The ratio tends to one", Disp(ClaimBody()),
                "Normalize C by P(n-1). Its diagonal is one, and an off-diagonal entry with positive modular displacement d is at most (6/5)/(12/5)^d. A cycle is reconstructed from a moved root and its displacement list. The positive displacements sum to a positive multiple of n. Counting all root and composition pairs bounds the total cycle weight by (6n/11)(11/12)^n/(1-(11/12)^n), which tends to zero. The permanent lies between one and the exponential of this weight, while the absolute determinant error is at most the permanent error. Both normalized functions tend to one; their common scalar factor cancels in the ratio.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("sp3921"), ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("pell-circulant-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula MatrixFormula()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var pell = new Formula.Apply(Qualified("D5", "S1", "Recurrence", "PellCompanionGcd", "P"),
            [Subtract(Subtract(n, D(1)), Call("val", k))]);
        var cast = Seq(new Formula.Apply(Qualified("Nat", "cast"), [pell]), Sp, Colon, Sp, Reals());
        var vector = Seq(Named("fun"), Sp,
            Parenthesized(Seq(k, Sp, Colon, Sp, Call("Fin", n))), Sp, Mapsto, Sp,
            Parenthesized(cast));
        return Disp(All("n", Naturals(), Equal(Call("C", n),
            new Formula.Apply(Qualified("Matrix", "circulant"), [Parenthesized(vector)]))));
    }

    private static Formula SequenceFormula(string name, string operation) => Disp(
        All("n", Naturals(), Equal(Call(name, F.Id("n")),
            new Formula.Apply(Qualified("Matrix", operation), [Call("C", F.Id("n"))]))));

    private static Formula ClaimBody()
    {
        var e = F.Id("epsilon");
        var threshold = F.Id("N");
        var n = F.Id("n");
        var ratio = new Formula.Fraction(Call("A392132", n), Call("A392131", n));
        var error = Seq(Lvert, Sp, Subtract(ratio, D(1)), Sp, Rvert);
        return All("epsilon", Reals(), Implication(Less(D(0), e),
            new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("N"), Naturals(),
                Conjunction(LessEqual(D(2), threshold), All("n", Naturals(),
                    Implication(LessEqual(threshold, n), Less(error, e)))))));
    }

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(params string[] names) =>
        Seq([.. names.SelectMany((name, index) => index == 0
            ? new[] { Named(name) } : new[] { Dot, Named(name) })]);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Implication(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Conjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
}
