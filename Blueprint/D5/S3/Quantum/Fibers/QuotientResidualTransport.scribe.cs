using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class QuotientResidualTransportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Isometric quotient transport preserves canonical residual norms and costs.",
        H("Quotient-Compatible Residual Transport"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("quotient-residual-transport-and-zero-set-countermodel"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Fibers/QuotientResidualTransport."
                        + "quotient_residual_transport_and_zero_set_countermodel"),
                H("Quotient transport preserves residual cost"),
                StatementSource.FromAuthor(TransportFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let the two charts be real-or-complex inner-product spaces with closed "
                            + "subspaces admitting orthogonal projections. A continuous linear "
                            + "transition preserves the subspaces and carries the two selected "
                            + "points to the same target quotient class.")),
                    Paragraph(Text(
                        "The quotient transition is constructed canonically with the quotient "
                            + "lift. When it is an isometry, the imported canonical quotient-to-"
                            + "orthogonal-complement equivalence identifies quotient norms with "
                            + "the norms of the two projection residuals. Their half-squared costs "
                            + "therefore agree.")),
                    Paragraph(Text(
                        "The final conjunct gives two explicit continuous linear residual maps on "
                            + "the real line. They have exactly the same zero set, but their costs "
                            + "at the displayed point differ, so zero-set agreement alone cannot "
                            + "supply cost invariance."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Norm(Formula value) =>
        Seq(Vert, Sp, value, Sp, Vert);

    private static Formula Squared(Formula value) =>
        new Formula.Power(value, Grp(D(2)));

    private static Formula Cost(Formula value) =>
        Seq(new Formula.Fraction(D(1), D(2)), Sp, Squared(Norm(value)));

    private static Formula TransportFormula()
    {
        Formula sourceSpace = Seq(F.Id("H"), Underscore, Grp(F.Id("k")));
        Formula targetSpace = Seq(F.Id("H"), Underscore, Grp(F.Id("j")));
        Formula sourceSubspace = Seq(F.Id("M"), Underscore, Grp(F.Id("k")));
        Formula targetSubspace = Seq(F.Id("M"), Underscore, Grp(F.Id("j")));
        Formula transition = Seq(F.Id("T"), Underscore, Grp(F.Id("k"), F.Id("j")));
        Formula quotientTransition = Seq(Overline, Grp(transition));
        Formula sourcePoint = Seq(F.Id("x"), Underscore, Grp(F.Id("k")));
        Formula targetPoint = Seq(F.Id("x"), Underscore, Grp(F.Id("j")));
        Formula sourceProjection = Seq(F.Id("P"), Underscore, Grp(sourceSubspace));
        Formula targetProjection = Seq(F.Id("P"), Underscore, Grp(targetSubspace));
        Formula sourceResidual = Seq(
            sourcePoint, Minus, Apply(sourceProjection, sourcePoint));
        Formula targetResidual = Seq(
            targetPoint, Minus, Apply(targetProjection, targetPoint));
        Formula first = F.Id("f");
        Formula second = F.Id("g");
        Formula point = F.Id("z");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula continuousLinearMap = Call("ContinuousLinearMap", real, real);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            sourceSubspace, Sp, Subset, Sp, sourceSpace, Comma, Sp,
            targetSubspace, Sp, Subset, Sp, targetSpace, Comma, Sp,
            transition, Colon, Sp, sourceSpace, Sp, To, Sp, targetSpace, Comma,
            RowBreak, Grp(),
            Apply(transition, sourceSubspace), Sp, Subset, Sp, targetSubspace, Comma, Sp,
            Apply(transition, sourcePoint), Sp, Minus, Sp, targetPoint, Sp,
            InMacro, Sp, targetSubspace, Comma,
            RowBreak, Grp(),
            quotientTransition, Open, OpenBracket, sourcePoint, CloseBracket, Close,
            Sp, Eq, Sp, OpenBracket, targetPoint, CloseBracket, Sp, Land, RowBreak, Grp(),
            Open, Call("Isometry", quotientTransition), Sp, Rightarrow, RowBreak, Grp(),
            Norm(sourceResidual), Sp, Eq, Sp, Norm(targetResidual), Sp, Land, RowBreak, Grp(),
            Cost(sourceResidual), Sp, Eq, Sp, Cost(targetResidual), Close,
            Sp, Land, RowBreak, Grp(),
            Exists, Sp, first, Comma, Sp, second, Colon, Sp, continuousLinearMap, Comma, Sp,
            point, InMacro, real, Comma, RowBreak, Grp(),
            Open, Forall, Sp, F.Id("x"), Comma, Sp,
            Apply(first, F.Id("x")), Sp, Eq, Sp, D(0), Sp, Leftrightarrow, Sp,
            Apply(second, F.Id("x")), Sp, Eq, Sp, D(0), Close, Sp, Land, RowBreak, Grp(),
            Cost(Apply(first, point)), Sp, Neq, Sp, Cost(Apply(second, point)), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
