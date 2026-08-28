using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.VisibleDescent;

internal sealed class LinearDescentCriterionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/VisibleDescent/LinearDescentCriterion.linear_descent_criterion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bounded linear descent through an orthogonal visible projection is equivalent to "
            + "vanishing hidden-to-visible carry and to projection-fiber dependence.",
        H("Linear Descent Criterion"),
        Blocks(Describe.Lean(
            DescribeId.Create("linear-descent-criterion"),
            DeclarationHandle.Create(Declaration),
            H("Orthogonal projection descent and the cross block"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The carrier is a Hilbert space, V is an orthogonally complemented visible "
                        + "subspace, P is its bounded orthogonal projection, and Q is projection "
                        + "onto the orthogonal complement. The ambient dynamics T is bounded and "
                        + "linear.")),
                Paragraph(Text(
                    "A commuting descent kills PTQ because P vanishes on the Q-range. Conversely, "
                        + "PTQ equal to zero makes PT constant on every P-fiber, since the "
                        + "difference of two states in one fiber lies in the hidden subspace.")),
                Paragraph(Text(
                    "Fiber dependence constructs the descent by including a visible vector, "
                        + "applying T, and projecting back with P. Surjectivity of P onto V makes "
                        + "every other commuting descent equal to this explicit restriction."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula scalar = F.Id("K");
        Formula space = F.Id("H");
        Formula visible = F.Id("V");
        Formula projection = F.Id("P");
        Formula hiddenProjection = F.Id("Q");
        Formula dynamics = F.Id("T");
        Formula descent = F.Id("Tbar");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula projectionDynamics = Seq(projection, Sp, Circ, Sp, dynamics);
        Formula crossBlock = Seq(
            projection, Sp, Circ, Sp, dynamics, Sp, Circ, Sp, hiddenProjection,
            Sp, Eq, Sp, D(0));
        Formula commutes = Seq(
            projectionDynamics, Sp, Eq, Sp,
            descent, Sp, Circ, Sp, projection);
        Formula existsDescent = Seq(
            Exists, Sp, descent, Colon, Sp, visible, Sp, To, Sp, visible,
            Comma, Sp, commutes);
        Formula fiberDependence = Seq(
            Forall, Sp, x, Comma, Sp, y, Colon, Sp, space, Comma, Sp,
            Apply(projection, x), Sp, Eq, Sp, Apply(projection, y),
            Sp, Rightarrow, Sp,
            Apply(Grp(projectionDynamics), x), Sp, Eq, Sp,
            Apply(Grp(projectionDynamics), y));
        Formula equivalence = Call(
            "TFAE", existsDescent, crossBlock, fiberDependence);
        Formula canonical = Call("restrictTo", projectionDynamics, visible);
        Formula canonicalCommutes = Seq(
            projectionDynamics, Sp, Eq, Sp, canonical, Sp, Circ, Sp, projection);
        Formula uniqueness = Seq(
            Forall, Sp, descent, Colon, Sp, visible, Sp, To, Sp, visible,
            Comma, Sp, Open, commutes, Close, Sp, Rightarrow, Sp,
            descent, Sp, Eq, Sp, canonical);
        Formula computedUniqueDescent = Seq(
            Open, crossBlock, Close, Sp, Rightarrow, Sp,
            Open, canonicalCommutes, Sp, Land, Sp, uniqueness, Close);

        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula submodule = Call("Submodule", scalar, space);
        Formula continuousMap = Call("ContinuousLinearMap", scalar, space, space);
        Formula setup = Seq(
            OpenBracket, Call("RCLike", scalar), CloseBracket, Comma, Sp,
            OpenBracket, Call("NormedAddCommGroup", space), CloseBracket, Comma, Sp,
            OpenBracket, Call("InnerProductSpace", scalar, space), CloseBracket, Comma, Sp,
            visible, Colon, Sp, submodule, Comma, Sp,
            OpenBracket, Call("HasOrthogonalProjection", visible), CloseBracket, Comma, Sp,
            dynamics, Colon, Sp, continuousMap, Comma, Sp,
            projection, Colon, Sp, continuousMap, Comma, Sp,
            hiddenProjection, Colon, Sp, continuousMap, Comma, RowBreak, Grp(),
            projection, Sp, Eq, Sp, Call("orthogonalProjectionOnto", visible), Comma, Sp,
            hiddenProjection, Sp, Eq, Sp, Call("starProjection", Seq(visible, Caret, Grp(Perp))));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, scalar, Comma, Sp, space, Colon, Sp, type, Comma, RowBreak, Grp(),
            setup, Sp, Rightarrow, RowBreak, Grp(),
            Open, equivalence, Close, Sp, Land,
            RowBreak, Grp(),
            Open, computedUniqueDescent, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);
}
