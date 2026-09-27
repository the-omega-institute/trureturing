using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumContext;

internal sealed class SingularSupportCandidateDiagonalizableDocument : IScribeDocumentDefinition
{
    private const string LeanPrefix =
        "D5/S3/QuantumContext/SingularSupportCandidateDiagonalizable.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive singular-support candidate columns admit an explicit real diagonalization.",
        H("Positive Singular-Support Columns and Diagonalization"),
        Blocks(
            Definition(
                "singular-support-radius",
                "r",
                "The singular-support radius",
                RadiusFormula(),
                "The radius combines the distinguished positive coordinate with the two support coordinates."),
            Definition(
                "unnormalized-support-block",
                "gZero",
                "The unnormalized support block",
                GZeroFormula(),
                "The support block is a positive scalar identity plus a positive rank-one matrix."),
            Definition(
                "column-normalization",
                "H",
                "The column-normalization matrix",
                HFormula(),
                "Each diagonal entry normalizes one support column by its radius and planar length."),
            Definition(
                "normalized-support-block",
                "K",
                "The normalized support block",
                KFormula(),
                "Right multiplication by the diagonal normalization rescales the two columns of the support block."),
            Definition(
                "distinguished-eigenvalue",
                "q",
                "The distinguished eigenvalue",
                QScalarFormula(),
                "The distinguished eigenvalue is the radius-normalized sum of the two weighted planar lengths."),
            Definition(
                "positive-final-column",
                "u",
                "The final candidate column",
                UFormula(),
                "The final column is the scaled residual of the distinguished eigenvalue equation on the positive support vector."),
            Definition(
                "three-dimensional-block-candidate",
                "Q",
                "The three-dimensional block candidate",
                QMatrixFormula(),
                "The candidate is block upper triangular with support block K, final column u, and scalar block q."),
            Describe.Lean(
                DescribeId.Create("positive-columns-and-explicit-real-diagonalization"),
                DeclarationHandle.Create(
                    LeanPrefix + "singular_support_candidate_positive_and_diagonalizable"),
                H("Positive columns and explicit real diagonalization"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For each component, eliminating the radial factor gives the displayed two-coordinate positivity identity. The ratio of the two diagonal normalizations is strictly below the corresponding square-root bound, which makes both residual components positive.")),
                    Paragraph(Text(
                        "The unnormalized support block is positive definite. Conjugating it by the positive square root of the normalization gives a real symmetric positive-definite matrix. Its spectral decomposition supplies two positive eigenvalues and an invertible eigenbasis for K.")),
                    Paragraph(Text(
                        "The identity Kp+zu=qp makes every weighted row sum strictly smaller than q. Applying the maximum-ratio argument to an eigenvector places both support eigenvalues below q.")),
                    Paragraph(Text(
                        "Adjoining p/z to the support eigenbasis gives the explicit upper-triangular block change of basis. The relation Kp+zu=qp proves the final column equation, and invertibility follows because the change of basis is block upper-triangular with invertible diagonal blocks."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(
        string id,
        string declaration,
        string heading,
        Formula formula,
        string prose) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(LeanPrefix + declaration),
            H(heading),
            StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))),
            DescribeRole.Definition);

    private static Formula RadiusFormula() => Disp(Seq(
        Typed(F.Id("z"), Real()), Comma, Sp,
        Typed(F.Id("p"), Arrow(Fin(2), Real())), Sp, Rightarrow, Sp,
        Call("r", F.Id("z"), F.Id("p")), Sp, Eq, Sp,
        Root(Seq(Square(F.Id("z")), Plus, Square(At(F.Id("p"), D(0))), Plus,
            Square(At(F.Id("p"), D(1))))), Dot));

    private static Formula GZeroFormula() => Disp(Seq(
        Typed(F.Id("z"), Real()), Comma, Sp,
        Typed(F.Id("p"), Arrow(Fin(2), Real())), Sp, Rightarrow, Sp,
        Call("gZero", F.Id("z"), F.Id("p")), Sp, Eq, Sp,
        F.Id("z"), Sp, Call("r", F.Id("z"), F.Id("p")), Sp, At(F.Id("I"), D(2)),
        Sp, Plus, Sp,
        Fraction(Call("r", F.Id("z"), F.Id("p")),
            Seq(Call("r", F.Id("z"), F.Id("p")), Plus, F.Id("z"))), Sp,
        Call("vecMulVec", F.Id("p"), F.Id("p")), Dot));

    private static Formula HFormula() => Disp(Seq(
        Typed(F.Id("z"), Real()), Comma, Sp,
        Typed(F.Id("p"), Arrow(Fin(2), Real())), Comma, Sp,
        Call("H", F.Id("z"), F.Id("p")), Sp, Eq, Sp,
        Call("diagonal", Seq(Open, F.Id("j"), Sp, Mapsto, Sp,
            Fraction(At(F.Id("p"), F.Id("j")),
                Seq(Call("r", F.Id("z"), F.Id("p")), Sp,
                    Root(Seq(Square(F.Id("z")), Plus, Square(At(F.Id("p"), F.Id("j"))))))),
            Close)), Dot));

    private static Formula KFormula() => Disp(Seq(
        Typed(F.Id("z"), Real()), Comma, Sp,
        Typed(F.Id("p"), Arrow(Fin(2), Real())), Sp, Rightarrow, Sp,
        Call("K", F.Id("z"), F.Id("p")), Sp, Eq, Sp,
        Call("gZero", F.Id("z"), F.Id("p")), Sp,
        Call("H", F.Id("z"), F.Id("p")), Dot));

    private static Formula QScalarFormula() => Disp(Seq(
        Typed(F.Id("z"), Real()), Comma, Sp,
        Typed(F.Id("p"), Arrow(Fin(2), Real())), Sp, Rightarrow, Sp,
        Call("q", F.Id("z"), F.Id("p")), Sp, Eq, Sp,
        Fraction(D(1), Call("r", F.Id("z"), F.Id("p"))), Sp,
        Sum, Underscore, Grp(F.Id("j"), Sp, InMacro, Sp, Fin(2)), Sp,
        At(F.Id("p"), F.Id("j")), Sp,
        Root(Seq(Square(F.Id("z")), Plus, Square(At(F.Id("p"), F.Id("j"))))), Dot));

    private static Formula UFormula() => Disp(Seq(
        Typed(F.Id("z"), Real()), Comma, Sp,
        Typed(F.Id("p"), Arrow(Fin(2), Real())), Sp, Rightarrow, Sp,
        Call("u", F.Id("z"), F.Id("p")), Sp, Eq, Sp,
        Fraction(D(1), F.Id("z")), Sp,
        Open, Call("q", F.Id("z"), F.Id("p")), Sp, At(F.Id("I"), D(2)), Sp,
        Minus, Sp, Call("K", F.Id("z"), F.Id("p")), Close, Sp, F.Id("p"), Dot));

    private static Formula QMatrixFormula() => Disp(Seq(
        Typed(F.Id("z"), Real()), Comma, Sp,
        Typed(F.Id("p"), Arrow(Fin(2), Real())), Sp, Rightarrow, Sp,
        Call("Q", F.Id("z"), F.Id("p")), Sp, Eq, Sp,
        Call("fromBlocks", Call("K", F.Id("z"), F.Id("p")),
            Call("u", F.Id("z"), F.Id("p")), D(0), Call("q", F.Id("z"), F.Id("p"))), Dot));

    private static Formula TheoremFormula()
    {
        Formula z = F.Id("z"), p = F.Id("p"), i = F.Id("i"), j = F.Id("j");
        Formula lambdaOne = At(F.LambdaLower, D(1));
        Formula lambdaTwo = At(F.LambdaLower, D(2));
        Formula finTwo = Fin(2);
        Formula blockIndex = Call("Sum", finTwo, Fin(1));
        Formula blockMatrix = Call("Matrix", blockIndex, blockIndex, Real());
        Formula diagonal = Call("fromBlocks",
            Call("diagonal", Seq(Bang, OpenBracket, lambdaOne, Comma, Sp, lambdaTwo, CloseBracket)),
            D(0), D(0), Call("const", Call("q", z, p)));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(z, Real()), Comma, Sp,
            Typed(p, Arrow(finTwo, Real())), Comma, RowBreak, Sp,
            D(0), Sp, Lt, Sp, z, Sp, Land, Sp,
            Open, Forall, Sp, Typed(j, finTwo), Comma, Sp,
            D(0), Sp, Lt, Sp, At(p, j), Close, Sp, Rightarrow, Sp, RowBreak, Sp,
            Open, Forall, Sp, Typed(j, finTwo), Comma, Sp,
            D(0), Sp, Lt, Sp, At(Call("u", z, p), j), Close, Sp, Land, Sp, RowBreak, Sp,
            Open, Forall, Sp, Typed(i, finTwo), Comma, Sp, Typed(j, finTwo), Comma, Sp,
            D(0), Sp, Lt, Sp, At(Call("K", z, p), i, j), Close, Sp, Land, Sp, RowBreak, Sp,
            Exists, Sp, Typed(lambdaOne, Real()), Comma, Sp, Typed(lambdaTwo, Real()), Comma, Sp,
            D(0), Sp, Lt, Sp, lambdaOne, Sp, Land, Sp,
            lambdaOne, Sp, Lt, Sp, Call("q", z, p), Sp, Land, Sp,
            D(0), Sp, Lt, Sp, lambdaTwo, Sp, Land, Sp,
            lambdaTwo, Sp, Lt, Sp, Call("q", z, p), Sp, Land, Sp, RowBreak, Sp,
            Exists, Sp, Typed(F.Id("S"), blockMatrix), Comma, Sp,
            Call("IsUnit", Call("det", F.Id("S"))), Sp, Land, Sp, RowBreak, Sp,
            Call("Q", z, p), Sp, F.Id("S"), Sp, Eq, Sp,
            F.Id("S"), Sp, diagonal, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < args.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(args[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(Open, source, Close, Sp, To, Sp, target);

    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Fin(byte size) => Call("Fin", D(size));

    private static Formula Root(Formula value) => Seq(Sqrt, Grp(value));

    private static Formula Square(Formula value) => Seq(Grp(value), Caret, Grp(D(2)));

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        Seq(Frac, Grp(numerator), Grp(denominator));

    private static Formula At(Formula value, params Formula[] indices) =>
        Seq(value, Underscore, Grp(Seq(indices)));
}
