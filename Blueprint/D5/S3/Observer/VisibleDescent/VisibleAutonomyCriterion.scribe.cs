using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.VisibleDescent;

internal sealed class VisibleAutonomyCriterionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/VisibleDescent/VisibleAutonomyCriterion.visible_autonomy_criterion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Visible-state descent, kernel stability, and zero hidden-to-visible flow are equivalent "
            + "for every idempotent linear projection.",
        H("Visible Autonomy Criterion"),
        Blocks(Describe.Lean(
            DescribeId.Create("visible-autonomy-criterion"),
            DeclarationHandle.Create(Declaration),
            H("Visible autonomy through an idempotent projection"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The visible state is constructed canonically by restricting an idempotent "
                        + "linear projection to its range. The next visible state is the range-valued "
                        + "restriction of projection after the ambient dynamics.")),
                Paragraph(Text(
                    "A descended range endomorphism exists exactly when the projection kernel is "
                        + "stable under the next-visible map, equivalently when the complementary "
                        + "hidden component has zero flow into the next visible state.")),
                Paragraph(Text(
                    "The imported two-coordinate rational example uses the same visible projection, "
                        + "hidden complement, and update in both cross blocks. Its hidden-to-visible "
                        + "block vanishes while the reverse block does not, so the criterion is "
                        + "strictly one-sided."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula scalar = F.Id("R");
        Formula space = F.Id("X");
        Formula projection = F.Id("P");
        Formula dynamics = F.Id("T");
        Formula complement = F.Id("Q");
        Formula visibleRange = F.Id("V");
        Formula visible = F.Id("visible");
        Formula visibleAfter = F.Id("visibleAfter");
        Formula descended = F.Id("descended");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula endomorphism = Call("LinearMap", scalar, space, space);
        Formula visibleEndomorphism = Call(
            "LinearMap", scalar, visibleRange, visibleRange);
        Formula projectionDynamics = Compose(projection, dynamics);

        Formula factorization = Seq(
            Exists, Sp, descended, Colon, Sp, visibleEndomorphism, Comma, Sp,
            visibleAfter, Sp, Eq, Sp, Compose(descended, visible));
        Formula kernelInclusion = Seq(
            Call("ker", projection), Sp, Subseteq, Sp,
            Call("ker", projectionDynamics));
        Formula hiddenToVisible = Seq(
            Compose(projectionDynamics, complement), Sp, Eq, Sp, D(0));
        Formula clauses = Grp(
            OpenBracket,
            factorization, Comma, Sp,
            kernelInclusion, Comma, Sp,
            hiddenToVisible,
            CloseBracket);

        Formula coordinateVisible = F.Id("visibleCoordinateProjection");
        Formula coordinateHidden = F.Id("hiddenCoordinateProjection");
        Formula coordinateLeak = F.Id("visibleToHiddenLeak");
        Formula coordinateIdempotent = Seq(
            Compose(coordinateVisible, coordinateVisible), Sp, Eq, Sp,
            coordinateVisible);
        Formula coordinateComplement = Seq(
            coordinateHidden, Sp, Eq, Sp, D(1), Sp, Minus, Sp,
            coordinateVisible);
        Formula coordinateHiddenToVisible = Seq(
            Compose(coordinateVisible, coordinateLeak, coordinateHidden),
            Sp, Eq, Sp, D(0));
        Formula coordinateVisibleToHidden = Seq(
            Compose(coordinateHidden, coordinateLeak, coordinateVisible),
            Sp, Neq, Sp, D(0));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, scalar, Comma, Sp, space, Colon, Sp, type, Comma),
            Seq(
                Call("Semiring", scalar), Sp, Land, Sp,
                Call("AddCommGroup", space), Sp, Land, Sp,
                Call("Module", scalar, space), Sp, Rightarrow),
            Seq(
                Forall, Sp, projection, Comma, Sp, dynamics, Colon, Sp,
                endomorphism, Comma),
            Seq(
                Compose(projection, projection), Sp, Eq, Sp, projection,
                Sp, Rightarrow),
            Seq(
                Operatorname, Grp(F.Id("let")), Sp,
                complement, Sp, Colon, Sp, Eq, Sp,
                D(1), Sp, Minus, Sp, projection, Comma),
            Seq(
                visibleRange, Sp, Colon, Sp, Eq, Sp,
                Call("range", projection), Comma),
            Seq(
                visible, Sp, Colon, Sp, Eq, Sp,
                Call("rangeRestrict", projection), Comma),
            Seq(
                visibleAfter, Sp, Colon, Sp, Eq, Sp,
                Call("codRestrict", visibleRange, projectionDynamics), Sp,
                Operatorname, Grp(F.Id("in"))),
            Seq(
                Call("ListTFAE", clauses), Sp, Land),
            Seq(
                Open, coordinateIdempotent, Sp, Land, Sp,
                coordinateComplement, Sp, Land),
            Seq(
                coordinateHiddenToVisible, Sp, Land, Sp,
                coordinateVisibleToHidden, Close, Dot),
        ]));
    }

    private static Formula Compose(params Formula[] maps)
    {
        var items = new List<Formula>();
        for (var index = 0; index < maps.Length; index++)
        {
            if (index > 0) items.AddRange([Sp, Circ, Sp]);
            items.Add(maps[index]);
        }
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula>
        {
            Operatorname,
            Grp(F.Id(name)),
            Open,
        };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
