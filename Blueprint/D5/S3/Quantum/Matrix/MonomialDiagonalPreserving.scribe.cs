using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class MonomialDiagonalPreservingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Monomial matrices admit a diagonal-times-permutation form and preserve diagonality "
            + "under the stated transpose sandwich.",
        H("Monomial Matrices Preserve Diagonality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("monomial-diagonal-preserving-monomial"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Matrix/MonomialDiagonalPreserving.monomial"),
                H("Monomial matrix"),
                StatementSource.FromAuthor(MonomialFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The monomial matrix attached to sigma and c places c(i) in row i at "
                            + "column sigma(i), and places zero at every other entry.")),
                    Paragraph(Text(
                        "This is the generalized permutation matrix pattern with row scalars. "
                            + "When every scalar is nonzero, every row and column has one "
                            + "nonzero entry."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("monomial-diagonal-preserving-diagonal-mul"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Matrix/MonomialDiagonalPreserving."
                        + "monomial_eq_diagonal_mul"),
                H("Diagonal-times-permutation form"),
                StatementSource.FromAuthor(DiagonalMulFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A monomial matrix is the permutation matrix of sigma multiplied on the "
                            + "left by the diagonal matrix of row scalars c."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("monomial-diagonal-preserving-transpose-sandwich"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Matrix/MonomialDiagonalPreserving."
                        + "isDiag_monomial_mul_diagonal_mul_transpose"),
                H("Diagonality after the transpose sandwich"),
                StatementSource.FromAuthor(DiagonalPreservingFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Multiplying a diagonal matrix on the left by a monomial matrix and on "
                            + "the right by its transpose permutes and rescales diagonal entries, "
                            + "so the resulting matrix remains diagonal.")),
                    Paragraph(Text(
                        "No converse is proved or claimed: the theorem does not say that every "
                            + "matrix preserving diagonality must be monomial."))),
                DescribeRole.Theorem))));

    private static Formula Monomial(Formula sigma, Formula scalars) =>
        Call("monomial", sigma, scalars);

    private static Formula MatrixDiagonal(Formula entries) =>
        Apply(Qualified("Matrix", "diagonal"), entries);

    private static Formula MatrixTranspose(Formula matrix) =>
        Apply(Qualified("Matrix", "transpose"), matrix);

    private static Formula PermutationMatrix(Formula sigma) =>
        Apply(
            Qualified("PEquiv", "toMatrix"),
            Apply(Qualified("Equiv", "toPEquiv"), sigma));

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

    private static Formula MonomialFormula()
    {
        Formula n = F.Id("n");
        Formula ring = F.Id("R");
        Formula sigma = F.Id("sigma");
        Formula c = F.Id("c");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula entry = Seq(
            Begin, Grp(F.Id("cases")),
            Apply(c, i), Comma, Amp,
            j, Sp, Eq, Sp, Apply(sigma, i), RowBreak,
            Num(0), Comma, Amp, F.Text, Grp(F.Id("otherwise")),
            End, Grp(F.Id("cases")));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Context(n, ring),
            Parameters(n, ring, sigma, c),
            Monomial(sigma, c), Sp, Eq, Sp,
            Apply(
                Qualified("Matrix", "of"),
                Seq(i, Comma, Sp, j, Sp, Mapsto, Sp, entry)),
            Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula DiagonalMulFormula()
    {
        Formula n = F.Id("n");
        Formula ring = F.Id("R");
        Formula sigma = F.Id("sigma");
        Formula c = F.Id("c");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Context(n, ring),
            Parameters(n, ring, sigma, c),
            Monomial(sigma, c), Sp, Eq, Sp,
            MatrixDiagonal(c), Sp, Cdot, Sp, PermutationMatrix(sigma), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula DiagonalPreservingFormula()
    {
        Formula n = F.Id("n");
        Formula ring = F.Id("R");
        Formula sigma = F.Id("sigma");
        Formula c = F.Id("c");
        Formula d = F.Id("d");
        Formula matrix = Seq(
            Monomial(sigma, c), Sp, Cdot, Sp, MatrixDiagonal(d), Sp, Cdot, Sp,
            MatrixTranspose(Monomial(sigma, c)));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Context(n, ring),
            Parameters(n, ring, sigma, c, d),
            Grp(matrix), Dot, Operatorname, Grp(F.Id("IsDiag")), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula TypeClass(Formula value) =>
        Seq(OpenBracket, value, CloseBracket);

    private static Formula Qualified(string owner, string member) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(member)));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
}
