using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class MonomialGramDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact diagonals obtained from monomial matrices and their transposes.",
        H("Gram Matrices of Monomial Matrices"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("monomial-gram-diagonal-transpose"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Matrix/MonomialGram."
                        + "monomial_mul_diagonal_mul_transpose"),
                H("Diagonal conjugation by a monomial matrix"),
                StatementSource.FromAuthor(DiagonalTransposeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Conjugating a diagonal matrix by a monomial matrix gives a diagonal "
                            + "matrix whose entry at i is the weight read at the permuted "
                            + "index sigma(i), times the square of the row scale c(i).")),
                    Paragraph(Text(
                        "No mixing occurs because a monomial matrix has at most one nonzero "
                            + "entry per "
                            + "row: a surviving term needs the same column index for two rows, "
                            + "which forces the rows equal because sigma is injective.")),
                    Paragraph(Text(
                        "The frozen isDiag_monomial_mul_diagonal_mul_transpose asserts only "
                            + "that this conjugate is diagonal, a property with no entry values; "
                            + "this module sharpens that to the exact diagonal, while the frozen "
                            + "statement is neither restated nor amended."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("monomial-gram-transpose"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Matrix/MonomialGram.monomial_mul_transpose"),
                H("Gram matrix of a monomial matrix"),
                StatementSource.FromAuthor(TransposeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Taking d = 1 gives the Gram matrix of the monomial matrix itself: its "
                            + "diagonal entries are the squares of the row scales."))),
                DescribeRole.Theorem))));

    private static Formula Monomial(Formula sigma, Formula scales) =>
        Call("monomial", sigma, scales);

    private static Formula MatrixDiagonal(Formula entries) =>
        Apply(Qualified("Matrix", "diagonal"), entries);

    private static Formula MatrixTranspose(Formula matrix) =>
        Apply(Qualified("Matrix", "transpose"), matrix);

    private static Formula Context(Formula n, Formula ring) =>
        Seq(
            Forall, Sp, n, Colon, Sp, F.Id("Type"), Comma, Sp,
            TypeClass(Call("DecidableEq", n)), Comma, Sp,
            TypeClass(Call("Fintype", n)), Comma, RowBreak,
            Forall, Sp, ring, Colon, Sp, F.Id("Type"), Comma, Sp,
            TypeClass(Call("CommRing", ring)), Comma, RowBreak);

    private static Formula Parameters(
        Formula n,
        Formula ring,
        Formula sigma,
        params Formula[] families)
    {
        var items = new List<Formula>
        {
            Forall, Sp, sigma, Colon, Sp,
            Apply(Qualified("Equiv", "Perm"), n), Comma, Sp
        };

        for (var index = 0; index < families.Length; index += 1)
        {
            items.Add(families[index]);
            if (index + 1 < families.Length)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
        }

        items.Add(Colon);
        items.Add(Sp);
        items.Add(n);
        items.Add(Sp);
        items.Add(To);
        items.Add(Sp);
        items.Add(ring);
        items.Add(Comma);
        items.Add(RowBreak);
        return Seq([.. items]);
    }

    private static Formula DiagonalTransposeFormula()
    {
        Formula n = F.Id("n");
        Formula ring = F.Id("R");
        Formula sigma = F.Id("sigma");
        Formula c = F.Id("c");
        Formula d = F.Id("d");
        Formula i = F.Id("i");
        Formula left = Seq(
            Monomial(sigma, c), Sp, Cdot, Sp, MatrixDiagonal(d), Sp, Cdot, Sp,
            MatrixTranspose(Monomial(sigma, c)));
        Formula entries = Seq(
            i, Sp, Mapsto, Sp, Apply(d, Apply(sigma, i)), Sp, Cdot, Sp,
            Apply(c, i), Caret, Num(2));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Context(n, ring),
            Parameters(n, ring, sigma, c, d),
            left, Sp, Eq, Sp, MatrixDiagonal(entries), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula TransposeFormula()
    {
        Formula n = F.Id("n");
        Formula ring = F.Id("R");
        Formula sigma = F.Id("sigma");
        Formula c = F.Id("c");
        Formula i = F.Id("i");
        Formula left = Seq(
            Monomial(sigma, c), Sp, Cdot, Sp,
            MatrixTranspose(Monomial(sigma, c)));
        Formula entries = Seq(i, Sp, Mapsto, Sp, Apply(c, i), Caret, Num(2));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Context(n, ring),
            Parameters(n, ring, sigma, c),
            left, Sp, Eq, Sp, MatrixDiagonal(entries), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula TypeClass(Formula value) =>
        Seq(OpenBracket, value, CloseBracket);

    private static Formula Qualified(string owner, string member) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(member)));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
}
