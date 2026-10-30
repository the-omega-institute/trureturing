using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.CubicGain;

internal sealed class LegalMatrixMonoidDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native forward words coincide with all nonnegative integral matrices of determinant plus or minus one.",
        H("The exact legal matrix monoid"),
        Blocks(
            Paragraph(Text("Mat is the full real 2 by 2 matrix space, and i,j range over Fin 2, displayed as {0,1}. A Boolean word u is a finite chronological list: false selects M=[[0,1],[1,1]], true selects J=[[0,1],[1,0]], and its head acts first. Write T(u)=futureProduct(u). The existing recursion is T([])=I and T(e::u)=T(u)E(e). In particular chronological M,J has matrix JM=U=[[1,1],[0,1]], while chronological J,M has matrix MJ=L=[[1,0],[1,1]].")),
            Describe.Lean(DescribeId.Create("chronological-native-product-append"),
                DeclarationHandle.Create("D5/S3/Observer/CubicGain/LegalMatrixMonoid.product_append"),
                H("Concatenation executes the earlier word first"),
                StatementSource.FromAuthor(AppendStatement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary finite words u,v, including empty words, chronological concatenation gives T(u++v)=T(v)T(u). Induction on u follows the existing product recursion and matrix associativity. This identity relates the actual cumulative endpoints and also cancels the adjacent J pairs when every multiplier is conjugated."))),
                DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("native-legal-matrix-monoid"),
                DeclarationHandle.Create("D5/S3/Observer/CubicGain/LegalMatrixMonoid.legal_matrix_monoid"),
                H("Exact forward-word characterization"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Every real matrix H is included in the displayed equivalence. The right side says each entry is nonnegative and is the real cast of an integer, and the determinant is either 1 or -1. The left side supplies an actual finite list of native forward actions. There are no entry or word-length bounds. I is represented by the empty list, J by [true], and matrices with zero entries are retained.")),
                    Paragraph(Text("For every word, induction constructs a natural four-entry matrix whose real cast is exactly its existing product T(u). Matrix multiplication commutes with this cast. This proves integrality and nonnegativity of the actual product. Both native factors have determinant -1, so every finite product has one of the two determinant signs.")),
                    Paragraph(Text("Conversely, nonnegative integral real entries have natural representatives. At determinant 1, the natural matrix generation theorem constructs an L/U word. Replacing each factor by its chronological native pair gives exactly the real product, with reversal handled by T(u++v)=T(v)T(u). At determinant -1, exchange the rows to obtain determinant 1, construct its word, then append J to exchange them back. All subtractions occur only in the natural parent proof. The acquired word contains M and J alone.")),
                    Paragraph(Text("The characterization supplies the monoid step used by exact cumulative continuation and by later legal-prefix normal forms. Those conclusions, their rank conditions and their additional endpoint filters are not asserted here."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, Formula x) =>
        Seq(Operatorname, Grp(F.Id(name)), Open, x, Close);
    private static Formula Entry(Formula h, Formula i, Formula j) =>
        Seq(h, Underscore, Grp(Seq(i, j)));
    private static Formula AppendStatement() => Disp(Seq(
        Forall, Sp, F.Id("u"), Comma, F.Id("v"), Comma, Sp,
        Call("T", Seq(F.Id("u"), Plus, Plus, F.Id("v"))), Eq, Sp,
        Call("T", F.Id("v")), Call("T", F.Id("u"))));
    private static Formula Statement()
    {
        var h = F.Id("H"); var u = F.Id("u");
        var i = F.Id("i"); var j = F.Id("j"); var z = F.Id("z");
        var indices = Seq(OpenBrace, D(0), Comma, D(1), CloseBrace);
        var words = Seq(OpenBrace, D(0), Comma, D(1), CloseBrace, Caret, Grp(Star));
        var entry = Entry(h, i, j);
        return Disp(Seq(
            Forall, Sp, h, InMacro, Sp, Mathbb, Grp(F.Id("R")),
            Caret, Grp(Seq(D(2), Times, D(2))), Comma, Sp,
            Open, Exists, Sp, u, InMacro, Sp, words, Comma, Sp,
            Call("T", u), Eq, Sp, h, Close, Iff, Sp,
            Open, Forall, Sp, i, Comma, j, InMacro, Sp, indices, Comma, Sp,
            Open, D(0), Leq, Sp, entry, Land, Sp,
            Exists, Sp, z, InMacro, Sp, Mathbb, Grp(F.Id("Z")), Comma, Sp,
            entry, Eq, Sp, z, Close, Close, Land, Sp,
            Open, Call("det", h), Eq, Sp, D(1), Lor, Sp,
            Call("det", h), Eq, Sp, Minus, D(1), Close));
    }
}
