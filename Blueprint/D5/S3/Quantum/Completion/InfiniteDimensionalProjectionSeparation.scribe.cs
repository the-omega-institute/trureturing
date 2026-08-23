using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Completion;

internal sealed class InfiniteDimensionalProjectionSeparationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dense finite-dimensional Hilbert projection towers converge on every vector while "
            + "remaining a unit operator-norm distance from the identity.",
        H("Infinite-Dimensional Projection Separation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("dense-finite-projection-towers-separate-pointwise-and-uniform-completion"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Completion/InfiniteDimensionalProjectionSeparation."
                        + "infinite_dimensional_projection_separation"),
                H("Dense finite projection towers complete pointwise but not uniformly"),
                StatementSource.FromAuthor(SeparationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let S be an increasing sequence of finite-dimensional closed subspaces "
                            + "of an infinite-dimensional Hilbert space, with cumulative closed "
                            + "span equal to the whole ambient space.")),
                    Paragraph(Text(
                        "No finite stage equals the ambient space. The canonical orthogonal "
                            + "projections nevertheless converge to the identity on every fixed "
                            + "vector, by the increasing-projection strong-limit theorem.")),
                    Paragraph(Text(
                        "At every stage, the identity-minus-projection operator is the orthogonal "
                            + "projection onto the nonzero complementary subspace. Its operator "
                            + "norm is therefore exactly one, so the norm sequence cannot converge "
                            + "to zero."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Projection(Formula stage, Formula vector) =>
        Apply(Call("P", stage), vector);

    private static Formula SeparationFormula()
    {
        Formula scalar = F.Id("K"), space = F.Id("H"), stages = F.Id("S");
        Formula n = F.Id("n"), x = F.Id("x");
        Formula stage = Apply(stages, n);
        Formula residualOperator = Seq(F.Id("I"), Sp, Minus, Sp, Call("P", stage));
        Formula residualNorm = new Formula.Norm(residualOperator);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, scalar, Comma, Sp, space, Comma, Sp,
            Call("Hilbert", scalar, space), Comma, Sp,
            Call("InfiniteDimensional", scalar, space), Comma, RowBreak,
            stages, Colon, Sp, Mathbb, Grp(F.Id("N")), Sp, To, Sp,
            Call("ClosedSubspace", space), Comma, Sp, Call("Monotone", stages), Comma,
            RowBreak,
            Open, Forall, Sp, n, Comma, Sp,
            Call("FiniteDimensional", scalar, stage), Close, Comma, Sp,
            Call("Cumulative", stages), Sp, Eq, Sp, space, Comma, RowBreak,
            Open, Forall, Sp, n, Comma, Sp, stage, Sp, Neq, Sp, space, Close,
            Sp, Land, RowBreak,
            Open, Forall, Sp, x, InMacro, Sp, space, Comma, Sp,
            Call("lim", n, Infty, Projection(stage, x)), Sp, Eq, Sp, x, Close,
            Sp, Land, RowBreak,
            Neg, Sp, Open, Call("lim", n, Infty, residualNorm), Sp, Eq, Sp, D(0), Close,
            Sp, Land, RowBreak,
            Open, Forall, Sp, n, Comma, Sp, residualNorm, Sp, Eq, Sp, D(1), Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
