using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class RatajczakTTransformDeterminantDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Algebraic/RatajczakTTransformDeterminant.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/ratajczak2021a110491");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ratajczak's literal T-transform determinant equals the independently specified A110491 sequence in every positive matrix order.",
        H("Ratajczak's A110491 T-Transform Determinant"),
        Blocks(
            Paragraph(Text(
                "Natural sequence indices start at zero, while matrix row and column "
                    + "indices in the source start at one. For a zero-based finite index, "
                    + "i1=val(i)+1 and j1=val(j)+1 implement that conversion. The lower "
                    + "branch remains literally sourceB(2*j1); it is not simplified to one "
                    + "inside the matrix definition. Matrix entries and determinants are "
                    + "integers. The sourceA sequence is specified independently by its two "
                    + "initial values and order-two recurrence, not by a determinant.")),
            Node("source-b", "The A093178 source sequence", "sourceB", SourceBFormula(),
                "The source sequence is one at even indices and is the index itself at odd "
                    + "indices. Although only positive arguments occur in the source matrix, "
                    + "the declaration is total on the natural numbers.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("source-a", "The independent A110491 recurrence", "sourceA", SourceAFormula(),
                "The target sequence starts with 1 and 2. Its next value is twice the "
                    + "preceding value plus 4(m+1)m times the value two positions back. "
                    + "This recurrence fixes every integer value independently of the matrix.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("source-matrix", "The literal T-transform matrix", "sourceMatrix",
                SourceMatrixFormula(),
                "The finite matrix uses the source's one-based i and j. Strictly below the "
                    + "diagonal its entry is sourceB(2*j1); on and above the diagonal its "
                    + "entry is sourceB(i1+j1-1). Thus the formal object retains both the "
                    + "source indexing and the stated lower branch exactly.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The all-order determinant identity", "result", ResultFormula(),
                "Subtracting each predecessor row leaves a leading one and reduces the "
                    + "determinant to the m-by-m matrix H. Conjugation by the alternating-sign "
                    + "diagonal extracts the factor 2^m and leaves the floor-linear matrix L. "
                    + "Subtracting each adjacent predecessor column from its successor "
                    + "converts L to the parity-upper matrix B. Multiplication by U2, the "
                    + "identity minus the second-superdiagonal matrix, has determinant one "
                    + "and converts B to the "
                    + "signed tridiagonal matrix T with diagonal one, subdiagonal p and "
                    + "superdiagonal -p. Reversing its indices and expanding the sparse "
                    + "front gives d_(m+2)=d_(m+1)+(m+1)m d_m. After restoring 2^m this is "
                    + "exactly the sourceA recurrence. The empty and one-dimensional "
                    + "determinants supply the m=0 and m=1 base cases, so the equality holds "
                    + "for every natural m, equivalently every positive matrix order m+1.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a110491-ratajczak-t-transform-determinant"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(
        string id,
        string title,
        string declaration,
        Formula formula,
        string prose,
        DescribeRole role,
        AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
            DescribeId.Create("a110491-" + id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role,
            claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula GreaterThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.GreaterThan, right);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Universal(string name, Formula type, Formula body) =>
        Disp(Seq(Bound(name, type), body));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula CastInteger(Formula value) =>
        Parenthesized(Seq(value, Colon, Sp, Integers()));

    private static Formula SourceBFormula()
    {
        var r = F.Id("r");
        return Universal("r", Naturals(), Equal(Call("sourceB", r),
            Call("ite", Call("Even", r), D(1), CastInteger(r))));
    }

    private static Formula SourceAFormula()
    {
        var m = F.Id("m");
        var recurrence = Equal(Call("sourceA", Add(m, D(2))),
            Add(Multiply(D(2), Call("sourceA", Add(m, D(1)))),
                Multiply(Multiply(Multiply(D(4), CastInteger(Add(m, D(1)))),
                    CastInteger(m)), Call("sourceA", m))));
        return Disp(new Formula.Aligned([
            Equal(Call("sourceA", D(0)), D(1)),
            Equal(Call("sourceA", D(1)), D(2)),
            Seq(Bound("m", Naturals()), recurrence)
        ]));
    }

    private static Formula SourceMatrixFormula()
    {
        var n = F.Id("n");
        var i = F.Id("i");
        var j = F.Id("j");
        var i1 = Add(Call("val", i), D(1));
        var j1 = Add(Call("val", j), D(1));
        var entry = Call("ite", GreaterThan(i1, j1),
            Call("sourceB", Multiply(D(2), j1)),
            Call("sourceB", Subtract(Add(i1, j1), D(1))));
        return Disp(Seq(
            Bound("n", Naturals()),
            Bound("i", Fin(n)),
            Bound("j", Fin(n)),
            Equal(Call("sourceMatrix", n, i, j), entry)));
    }

    private static Formula ResultFormula()
    {
        var m = F.Id("m");
        return Universal("m", Naturals(),
            Equal(Call("det", Call("sourceMatrix", Add(m, D(1)))), Call("sourceA", m)));
    }
}
