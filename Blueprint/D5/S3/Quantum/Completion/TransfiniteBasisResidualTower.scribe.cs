using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Completion;

internal sealed class TransfiniteBasisResidualTowerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An initially indexed infinite Hilbert basis determines successor splittings, exact "
            + "limit stages, full-size proper residuals, and a zero terminal residual.",
        H("Transfinite Hilbert-Basis Residual Tower"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("initial-hilbert-basis-transfinite-residual-tower"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Completion/TransfiniteBasisResidualTower."
                        + "transfinite_basis_residual_tower"),
                H("Initially indexed bases split every residual stage"),
                StatementSource.FromAuthor(TowerFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a Hilbert basis indexed by an infinite initial well-order, the "
                            + "prefix at a set of indices is its closed linear span and the "
                            + "residual is the orthogonal complement of that prefix.")),
                    Paragraph(Text(
                        "A successor stage splits off the current basis line orthogonally. At "
                            + "a limit index, the prefix is the closed supremum of earlier "
                            + "prefixes and the residual is their intersection.")),
                    Paragraph(Text(
                        "Every proper initial segment leaves an index complement of the original "
                            + "cardinality. The displayed isometry sends each named tail vector "
                            + "to its reindexed ambient basis vector, while the full-index "
                            + "residual is zero."))),
                DescribeRole.Theorem))));

    private static Formula Sub(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula Prefix(Formula basis, Formula indices) =>
        Call("Prefix", basis, indices);

    private static Formula Residual(Formula basis, Formula indices) =>
        Call("Residual", basis, indices);

    private static Formula TowerFormula()
    {
        Formula scalar = F.Id("K"), space = F.Id("H"), index = F.Id("I");
        Formula basis = F.Id("b"), i = F.Id("i"), j = F.Id("j");
        Formula lower = Call("Iio", i), lowerClosed = Call("Iic", i);
        Formula shell = Call("span", scalar, Sub(basis, i));
        Formula currentResidual = Residual(basis, lower);
        Formula nextResidual = Residual(basis, lowerClosed);
        Formula tail = Seq(index, Sp, Setminus, Sp, lower);
        Formula isometry = Sub(F.Id("E"), i);
        Formula tailVector = Sub(F.Id("t"), j);
        Formula reindex = Sub(F.Id("epsilon"), i);
        Formula fullPrefix = Prefix(basis, index);
        Formula fullResidual = Residual(basis, index);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, scalar, Comma, Sp, space, Comma, Sp, index, Comma, Sp, basis, Comma,
            RowBreak, Grp(),
            Call("Hilbert", scalar, space), Comma, Sp,
            Call("InfiniteInitialWellOrder", index), Comma, Sp,
            Call("HilbertBasis", basis, index, scalar, space), Comma, RowBreak, Grp(),
            Open, Forall, Sp, i, InMacro, Sp, index, Comma, Sp,
            currentResidual, Sp, Eq, Sp, Call("DirectSum", shell, nextResidual), Sp, Land, Sp,
            Call("Orthogonal", shell, nextResidual), Close, Sp, Land, RowBreak, Grp(),
            Open, Open, Forall, Sp, i, InMacro, Sp, index, Comma, Sp, Call("Limit", i), Sp,
            Rightarrow, Sp,
            Prefix(basis, lower), Sp, Eq, Sp,
            Call("ClosedSup", Sub(Prefix(basis, Call("Iio", j)), Seq(j, Lt, i))), Sp, Land, Sp,
            currentResidual, Sp, Eq, Sp,
            Call("Inf", Sub(Residual(basis, Call("Iio", j)), Seq(j, Lt, i))), Close,
            Sp, Land, RowBreak, Grp(),
            fullPrefix, Sp, Eq, Sp,
            Call("ClosedSup", Sub(Prefix(basis, Call("Iio", j)), Seq(j, InMacro, Sp, index))),
            Sp, Land, Sp, fullResidual, Sp, Eq, Sp,
            Call("Inf", Sub(Residual(basis, Call("Iio", j)), Seq(j, InMacro, Sp, index))),
            Close, Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, i, InMacro, Sp, index, Comma, Sp,
            Call("Card", tail), Sp, Eq, Sp, Call("Card", index), Sp, Land, Sp,
            Open, Forall, Sp, j, InMacro, Sp, tail, Comma, Sp,
            isometry, Open, tailVector, Close, Sp, Eq, Sp,
            basis, Open, reindex, Open, j, Close, Close, Close, Close,
            Sp, Land, RowBreak, Grp(),
            fullResidual, Sp, Eq, Sp, D(0), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
