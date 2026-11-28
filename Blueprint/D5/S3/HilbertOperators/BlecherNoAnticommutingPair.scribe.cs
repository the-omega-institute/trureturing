using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HilbertOperators;

internal sealed class BlecherNoAnticommutingPairDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/HilbertOperators/BlecherNoAnticommutingPair";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/HilbertOperators/blecher2025commutativity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A noncommutative symmetric operator algebra in M₁₆(ℂ) excludes nonzero anticommuting products.",
        H("A symmetric operator algebra without a nonzero anticommuting product"),
        Blocks(
            Describe.Lean(DescribeId.Create("claim"), DeclarationHandle.Create(Module + ".claim"),
                H("The necessity of a nonzero anticommuting product"),
                StatementSource.FromAuthor(Disp(Logic(LocalClaim(), FormulaLogicOperator.Iff, ClaimBody()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The proposed necessity applies to a complex subspace of M₁₆(ℂ) that is closed under matrix "
                    + "multiplication, has a noncommuting pair, and retains every Euclidean operator norm under "
                    + "entrywise transpose on matrix amplifications. The proposed pair has xy = −yx and xy ≠ 0. "
                    + "This is the pair condition in Blecher, Example 5.5."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Module + ".result"),
                H("A faithful sixteen-dimensional matrix representation gives a counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For a complex row r of length two and a two-by-two matrix Z, take a direct sum of four "
                        + "upper triangular blocks. In each block the outer slots have size one and the middle "
                        + "slot has size two. The three upper entries are r, the entry pairing of J with Z, and "
                        + "J times the transpose of r. The probes J are the identity, a single diagonal sign "
                        + "change, the coordinate swap and the signed coordinate swap with entries "
                        + "(0, −1; 1, 0).")),
                    Paragraph(Text(
                        "The product in each block has only its upper-right entry, the entry pairing of J with "
                        + "the outer product of the two rows. The top-middle block recovers r. Adding and "
                        + "subtracting the first two probe readings recovers the diagonal of Z. Adding and "
                        + "subtracting the last two recovers its off-diagonal entries. The resulting complex-linear "
                        + "map is injective and multiplicative. The two standard basis rows give distinct outer "
                        + "products in the two orders.")),
                    Paragraph(Text(
                        "If the two outer products are negatives of each other, choose a nonzero coordinate of "
                        + "the first row if it has one. The diagonal equation forces the corresponding coordinate "
                        + "of the second row to be zero. The other equations with that same row index then force "
                        + "the whole second row to be zero. Their product in the image is therefore zero.")),
                    Paragraph(Text(
                        "For each probe, use the unitary that exchanges the outer slots and acts by J on the "
                        + "middle slot. Multiplying the transpose of a block by this unitary on both sides "
                        + "recovers the original block. The direct sum of these unitaries gives the same identity "
                        + "on the image. At every matrix level its copies form a block diagonal unitary. "
                        + "Unitary multiplication on both sides preserves the assembled Euclidean operator norm. "
                        + "Transpose also reverses multiplication, so it realizes the reversed algebra "
                        + "completely isometrically.")),
                    Paragraph(Text(
                        "For each m ≥ 2 the same construction uses m² probes. There is one identity probe, "
                        + "m − 1 diagonal sign changes, and one unsigned swap and one signed swap for each "
                        + "unordered pair of distinct coordinates. Subtracting the signed swap reading from "
                        + "the unsigned swap reading recovers twice one off-diagonal entry. Comparing the "
                        + "unsigned swap reading to the identity reading recovers the other using the known "
                        + "diagonal. The representation is faithful in complex matrices of size m²(m + 2), and the same argument "
                        + "proves noncommutativity, the zero-product implication and all amplification "
                        + "norm equalities."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("blecher-2025-example-5-5-no-anticommuting-pair"),
                    ResolutionKind.Refuted)))));

    private static Formula ClaimBody()
    {
        Formula a = F.Id("A"), x = F.Id("x"), y = F.Id("y"), k = F.Id("k");
        Formula i = F.Id("i"), j = F.Id("j");
        Formula xy = Multiply(x, y), yx = Multiply(y, x);
        Formula closed = ForPair(true, Member(xy, a));
        Formula noncommutative = ForPair(false, Relation(xy, FormulaRelationOperator.NotEqual, yx));
        Formula badPair = ForPair(false, Logic(
            Relation(xy, FormulaRelationOperator.Equal, new Formula.Negate(Parenthesized(yx))),
            FormulaLogicOperator.And, Relation(xy, FormulaRelationOperator.NotEqual, D(0))));
        Formula entries = Bind(Forall, i, Fin(k), Bind(Forall, j, Fin(k), Member(At(x, i, j), a)));
        Formula transposed = BindLambda(i, Fin(k), BindLambda(j, Fin(k), At(Name("Matrix", "transpose"), At(x, i, j))));
        Formula norm = Relation(new Formula.Norm(Assemble(k, transposed)),
            FormulaRelationOperator.Equal, new Formula.Norm(Assemble(k, x)));
        Formula symmetric = Bind(Forall, k, Naturals(),
            Bind(Forall, x, Arrow(Fin(k), Arrow(Fin(k), Ambient())), Arrow(entries, norm)));
        return Bind(Forall, a, At(Name("Submodule"), Complexes(), Ambient()),
            Arrow(closed, Arrow(noncommutative, Arrow(symmetric, badPair))));
    }

    private static Formula ForPair(bool universal, Formula body)
    {
        Formula quantifier = universal ? Forall : Exists;
        return MemberBind(F.Id("x"), MemberBind(F.Id("y"), body));

        Formula MemberBind(Formula variable, Formula rest) =>
            Bind(quantifier, variable, Ambient(), universal
                ? Arrow(Member(variable, F.Id("A")), rest)
                : Logic(Member(variable, F.Id("A")), FormulaLogicOperator.And, rest));
    }

    private static Formula LocalClaim() => Name("D5", "S3", "HilbertOperators", "BlecherNoAnticommutingPair", "claim");
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Fin(Formula n) => At(Name("Fin"), n);
    private static Formula AmbientIndex() => Fin(D(1, 6));
    private static Formula Ambient() => At(Name("Matrix"), AmbientIndex(), AmbientIndex(), Complexes());
    private static Formula Assemble(Formula k, Formula x) =>
        At(Name("Matrix", "comp"), Fin(k), Fin(k), AmbientIndex(), AmbientIndex(), Complexes(), x);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Bind(Formula quantifier, Formula value, Formula type, Formula body) =>
        Seq(quantifier, Sp, Typed(value, type), Comma, Sp, Parenthesized(body));
    private static Formula BindLambda(Formula value, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(value, type), Sp, Mapsto, Sp, Parenthesized(body)));
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(Parenthesized(a), Parenthesized(b));
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Parenthesized(a), op, Parenthesized(b));
    private static Formula Relation(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Member(Formula a, Formula b) => Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Multiply(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);

    private static Formula Name(params string[] parts)
    {
        var tokens = new System.Collections.Generic.List<Formula>();
        foreach (string part in parts)
        {
            if (tokens.Count > 0) tokens.Add(Dot);
            tokens.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. tokens])));
    }
}
