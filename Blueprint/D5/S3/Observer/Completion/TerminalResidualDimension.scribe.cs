using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Completion;

internal sealed class TerminalResidualDimensionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The strict natural coordinate tails retain full dimension at every stage while "
            + "their terminal intersection is zero.",
        H("Constant Stage Dimension with Zero Terminal Residual"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("constant-dimension-zero-terminal"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Completion/TerminalResidualDimension."
                        + "constant_dimension_with_zero_terminal"),
                H("Full-sized coordinate tails have zero terminal intersection"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Use the same closed coordinate-tail chain in the real Hilbert space "
                            + "of square-summable natural-numbered sequences as in the earlier "
                            + "residual-progress theorem.")),
                    Paragraph(Text(
                        "Because the natural numbers contain no omega stage, the terminal is "
                            + "defined externally as the intersection of all natural stages. "
                            + "The transfinite residual theorem identifies this intersection "
                            + "with the residual after every basis coordinate is consumed.")),
                    Paragraph(Text(
                        "The zeroth stage is the whole space, every successor inclusion is "
                            + "strict, and every stage is linearly isometric to the "
                            + "infinite-dimensional ambient space. Nevertheless, the terminal "
                            + "intersection is the zero subspace.")),
                    Paragraph(Text(
                        "Empty and singleton index sets with a constant whole-space chain have "
                            + "nonzero intersection; constant zero chains have zero intersection. "
                            + "The theorem therefore makes no claim for arbitrary stage types."))),
                DescribeRole.Theorem))));

    private static Formula Sub(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula TheoremFormula()
    {
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula space = Call("ell", D(2), naturals);
        Formula residual = F.Id("R");
        Formula n = F.Id("n");
        Formula next = Seq(n, Sp, Plus, Sp, D(1));
        Formula terminal = Call("iInf", residual);

        return Disp(Seq(
            Exists, Sp, residual, Colon, Sp, naturals, Sp, To, Sp,
            Call("ClosedSubspace", space), Comma, Sp,
            Sub(residual, D(0)), Sp, Eq, Sp, Call("top", space), Sp, Land, RowBreak,
            Open, Forall, Sp, n, InMacro, Sp, naturals, Comma, Sp,
            Call("StrictSubset", Sub(residual, next), Sub(residual, n)), Close,
            Sp, Land, RowBreak,
            Open, Forall, Sp, n, InMacro, Sp, naturals, Comma, Sp,
            Call("LinearIsometric", reals, Sub(residual, n), space), Close,
            Sp, Land, RowBreak,
            Call("InfiniteDimensional", reals, space), Sp, Land, RowBreak,
            terminal, Sp, Eq, Sp, Call("zeroSubspace", space), Dot));
    }
}
