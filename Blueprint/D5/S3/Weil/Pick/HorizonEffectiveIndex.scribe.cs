using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Pick;

internal sealed class HorizonEffectiveIndexDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/Pick/HorizonEffectiveIndex.finite_hankel_horizon_effective_index";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Effective Hankel defect indices obey positivity, product, sum, and boundary laws.",
        H("Horizon Effective Index"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-hankel-horizon-effective-index"),
                DeclarationHandle.Create(Declaration),
                H("Finite Hankel horizon effective index"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Finite square real matrices model the finite-rank Hankel operators. "
                            + "Strict contraction is stated by requiring every spectrally "
                            + "defined singular value to be below one.")),
                    Paragraph(Text(
                        "The characteristic polynomial of the Hermitian Gram matrix, evaluated "
                            + "at one, gives the singular-value product for the defect "
                            + "determinant. Positivity makes the defect invertible and proves the "
                            + "reciprocal determinant and logarithmic formulas.")),
                    Paragraph(Text(
                        "Block determinants give orthogonal-sum multiplicativity, the zero "
                            + "matrix gives normalization and an explicit inhabited Hankel "
                            + "example, and the reciprocal singular factor tends to infinity at "
                            + "the contractive boundary.")),
                    Paragraph(Text(
                        "The declaration formalizes only the effective information index. It "
                            + "does not claim that a Jones index has been constructed."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula n = F.Id("n");
        Formula m = F.Id("m");
        Formula i = F.Id("i");
        Formula h = F.Id("H");
        Formula k = F.Id("K");
        Formula sigma = SigmaLower;
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula oneByOne = MatrixSpace(D(1));
        Formula defect = Call("horizonDefect", h);
        Formula index = Call("horizonEffectiveIndex", h);
        Formula singularFactor = Raised(
            Grp(Seq(
                D(1), Sp, Minus, Sp,
                Raised(Call("finiteSingularValue", h, i), D(2)))),
            Seq(Minus, D(1)));

        Formula contractiveHankelLaw = Seq(
            Open,
            Forall, Sp, n, Sp, InMacro, Sp, naturals, Comma, Sp,
            h, Sp, InMacro, Sp, MatrixSpace(n), Comma, Sp,
            Call("IsFiniteHankel", h), Sp, Land, Sp,
            Call("IsStrictlyContractive", h), Sp, Rightarrow, RowBreak, Grp(),
            Call("IsUnit", defect), Sp, Land, Sp,
            D(0), Sp, Lt, Sp, Call("det", defect), Sp, Land, RowBreak, Grp(),
            D(0), Sp, Lt, Sp, index, Sp, Land, Sp,
            index, Sp, Eq, Sp,
            Prod, Underscore,
            Grp(i, Sp, InMacro, Sp, Call("Fin", n)), Sp,
            singularFactor, Sp, Land, RowBreak, Grp(),
            Call("log", index), Sp, Eq, Sp, Minus,
            Call("log", Call("det", defect)),
            Close);

        Formula orthogonalSumLaw = Seq(
            Open,
            Forall, Sp, m, Comma, Sp, n, Sp, InMacro, Sp, naturals, Comma, Sp,
            h, Sp, InMacro, Sp, MatrixSpace(m), Comma, Sp,
            k, Sp, InMacro, Sp, MatrixSpace(n), Comma, Sp,
            Call("horizonEffectiveIndex", Call("orthogonalSum", h, k)),
            Sp, Eq, Sp, index, Sp, Times, Sp,
            Call("horizonEffectiveIndex", k),
            Close);

        Formula zeroLaw = Seq(
            Open,
            Forall, Sp, n, Sp, InMacro, Sp, naturals, Comma, Sp,
            Call("horizonEffectiveIndex", ZeroMatrix(n)), Sp, Eq, Sp, D(1),
            Close);

        Formula boundaryLaw = Seq(
            Open,
            Call(
                "Tendsto",
                Seq(Open, sigma, Sp, Mapsto, Sp, Raised(
                    Grp(Seq(D(1), Sp, Minus, Sp, Raised(sigma, D(2)))),
                    Seq(Minus, D(1))), Close),
                Call("nhdsWithin", D(1), Call("Iio", D(1))),
                F.Id("atTop")),
            Close);

        Formula inhabitedLaw = Seq(
            Open,
            Exists, Sp, h, Sp, InMacro, Sp, oneByOne, Comma, Sp,
            Call("IsFiniteHankel", h), Sp, Land, Sp,
            Call("IsStrictlyContractive", h), Sp, Land, Sp,
            index, Sp, Eq, Sp, D(1),
            Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            contractiveHankelLaw, Sp, Land, RowBreak, Grp(),
            orthogonalSumLaw, Sp, Land, RowBreak, Grp(),
            zeroLaw, Sp, Land, RowBreak, Grp(),
            boundaryLaw, Sp, Land, RowBreak, Grp(),
            inhabitedLaw, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula MatrixSpace(Formula dimension) =>
        Raised(
            Seq(Mathbb, Grp(F.Id("R"))),
            Seq(dimension, Sp, Times, Sp, dimension));

    private static Formula ZeroMatrix(Formula dimension) =>
        Seq(D(0), Underscore, Grp(dimension, Sp, Times, Sp, dimension));

    private static Formula Raised(Formula value, Formula exponent) =>
        Seq(value, Caret, Grp(exponent));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (int index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                pieces.Add(Comma);
                pieces.Add(Sp);
            }

            pieces.Add(arguments[index]);
        }

        pieces.Add(Close);
        return Seq(pieces.ToArray());
    }
}
