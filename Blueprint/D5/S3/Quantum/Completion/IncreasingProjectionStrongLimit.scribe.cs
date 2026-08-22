using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Completion;

internal sealed class IncreasingProjectionStrongLimitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Increasing orthogonal projections converge strongly to the cumulative projection and, "
            + "under terminal completeness, to the identity.",
        H("Increasing Projection Strong Limit"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("increasing-projections-have-the-cumulative-strong-limit"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Completion/IncreasingProjectionStrongLimit."
                        + "increasing_projection_strong_limit"),
                H("Increasing projections have the cumulative strong limit"),
                StatementSource.FromAuthor(StrongLimitFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let S be an increasing sequence of closed projection subspaces of a "
                            + "Hilbert space. Its cumulative space is the closure of the supremum "
                            + "of the finite stages, and its terminal residual is the orthogonal "
                            + "complement of that cumulative space.")),
                    Paragraph(Text(
                        "For every vector x, the orthogonal projections onto S(n) converge in "
                            + "norm to the orthogonal projection onto the cumulative space. This "
                            + "is the vectorwise form of the increasing-projection limit.")),
                    Paragraph(Text(
                        "When the terminal residual is zero, the cumulative space is the whole "
                            + "Hilbert space. The same vectorwise limits then assemble through "
                            + "Mathlib's pointwise-convergence topology on continuous linear maps, "
                            + "the strong operator topology, into convergence to the identity."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Projection(Formula stage, Formula vector) =>
        Apply(Call("P", stage), vector);

    private static Formula StrongLimitFormula()
    {
        Formula scalar = F.Id("K"), space = F.Id("H"), stages = F.Id("S");
        Formula n = F.Id("n"), x = F.Id("x");
        Formula cumulative = F.Id("Sinf"), residual = F.Id("Rinf");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, scalar, Comma, Sp, space, Comma, Sp,
            Call("Hilbert", scalar, space), Comma, RowBreak,
            stages, Colon, Sp, Mathbb, Grp(F.Id("N")), Sp, To, Sp,
            Call("ClosedSubspace", space), Comma, Sp, Call("Monotone", stages), Comma,
            RowBreak,
            cumulative, Sp, Eq, Sp, Overline, Grp(
                Call("iSup", n, Apply(stages, n))), Comma, Sp,
            residual, Sp, Eq, Sp, cumulative, Caret, Grp(Perp), Comma, RowBreak,
            Open, Forall, Sp, x, InMacro, Sp, space, Comma, Sp,
            Call("lim", n, Infty, Projection(Apply(stages, n), x)), Sp, Eq, Sp,
            Projection(cumulative, x), Close, Sp, Land, RowBreak,
            Open, residual, Sp, Eq, Sp, D(0), Sp,
            Rightarrow, Sp, Call("SOTlim", n, Infty, Call("P", Apply(stages, n))),
            Sp, Eq, Sp, F.Id("I"), Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
