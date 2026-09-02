using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class MonomialColumnGramDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Transposes of monomial matrices and their column-side diagonal products.",
        H("Transposes and Column Gram Matrices of Monomial Matrices"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("monomial-column-gram-transpose"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Matrix/MonomialColumnGram.monomial_transpose"),
                H("Transpose of a monomial matrix"),
                StatementSource.FromAuthor(MonomialTransposeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Transposing a monomial matrix gives a monomial matrix again, for the "
                            + "inverse permutation, with the scales relabelled along that "
                            + "inverse. This is the structural fact the module exists for."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("monomial-column-gram-diagonal"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Matrix/MonomialColumnGram."
                        + "transpose_mul_diagonal_mul_monomial"),
                H("Column-side diagonal conjugation"),
                StatementSource.FromAuthor(TransposeDiagonalMonomialFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The column-side conjugate is diagonal and is indexed by the inverse "
                            + "permutation: at j it is d at sigma inverse of j times the square "
                            + "of c at that same index.")),
                    Paragraph(Text(
                        "This identity is derived from monomial_transpose together with the "
                            + "frozen row-side identity "
                            + "monomial_mul_diagonal_mul_transpose, not recomputed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("monomial-column-gram-product"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Matrix/MonomialColumnGram.transpose_mul_monomial"),
                H("Column Gram matrix of a monomial matrix"),
                StatementSource.FromAuthor(TransposeMonomialFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Taking d = 1 gives the column Gram matrix, whose diagonal at j is the "
                            + "square of the scale relabelled by the inverse permutation.")),
                    Paragraph(Text(
                        "Nothing is asserted about unitary groups, spectra, eigenvalues, or any "
                            + "converse."))),
                DescribeRole.Theorem))));

    private static Formula Monomial(Formula sigma, Formula scales) =>
        Call("monomial", sigma, scales);

    private static Formula MatrixDiagonal(Formula entries) =>
        Apply(Qualified("Matrix", "diagonal"), entries);

    private static Formula MatrixTranspose(Formula matrix) =>
        Apply(Qualified("Matrix", "transpose"), matrix);

    private static Formula Inverse(Formula permutation) =>
        Seq(permutation, Caret, Grp(Minus, Num(1)));

    private static Formula ContextWithoutFintype(Formula n, Formula ring) =>
        Seq(
            Forall, Sp, n, Colon, Sp, F.Id("Type"), Comma, Sp,
            TypeClass(Call("DecidableEq", n)), Comma, RowBreak,
            Forall, Sp, ring, Colon, Sp, F.Id("Type"), Comma, Sp,
            TypeClass(Call("CommRing", ring)), Comma, RowBreak);

    private static Formula ContextWithFintype(Formula n, Formula ring) =>
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

    private static Formula MonomialTransposeFormula()
    {
        Formula n = F.Id("n");
        Formula ring = F.Id("R");
        Formula sigma = F.Id("sigma");
        Formula c = F.Id("c");
        Formula j = F.Id("j");
        Formula inverse = Inverse(sigma);
        Formula relabelled = Seq(j, Sp, Mapsto, Sp, Apply(c, Apply(inverse, j)));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            ContextWithoutFintype(n, ring),
            Parameters(n, ring, sigma, c),
            MatrixTranspose(Monomial(sigma, c)), Sp, Eq, Sp,
            Monomial(inverse, relabelled), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula TransposeDiagonalMonomialFormula()
    {
        Formula n = F.Id("n");
        Formula ring = F.Id("R");
        Formula sigma = F.Id("sigma");
        Formula c = F.Id("c");
        Formula d = F.Id("d");
        Formula j = F.Id("j");
        Formula inverseAtJ = Apply(Inverse(sigma), j);
        Formula left = Seq(
            MatrixTranspose(Monomial(sigma, c)), Sp, Cdot, Sp,
            MatrixDiagonal(d), Sp, Cdot, Sp, Monomial(sigma, c));
        Formula entries = Seq(
            j, Sp, Mapsto, Sp, Apply(d, inverseAtJ), Sp, Cdot, Sp,
            Apply(c, inverseAtJ), Caret, Num(2));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            ContextWithFintype(n, ring),
            Parameters(n, ring, sigma, c, d),
            left, Sp, Eq, Sp, MatrixDiagonal(entries), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula TransposeMonomialFormula()
    {
        Formula n = F.Id("n");
        Formula ring = F.Id("R");
        Formula sigma = F.Id("sigma");
        Formula c = F.Id("c");
        Formula j = F.Id("j");
        Formula inverseAtJ = Apply(Inverse(sigma), j);
        Formula left = Seq(
            MatrixTranspose(Monomial(sigma, c)), Sp, Cdot, Sp,
            Monomial(sigma, c));
        Formula entries = Seq(
            j, Sp, Mapsto, Sp, Apply(c, inverseAtJ), Caret, Num(2));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            ContextWithFintype(n, ring),
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
