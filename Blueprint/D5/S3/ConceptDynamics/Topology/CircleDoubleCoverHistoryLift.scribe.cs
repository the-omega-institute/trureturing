using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Topology;

internal sealed class CircleDoubleCoverHistoryLiftDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Topology/CircleDoubleCoverHistoryLift."
            + "circle_double_cover_history_lift";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The circle double cover has canonical history-dependent path lifts.",
        H("History Lifts in the Circle Double Cover"),
        Blocks(Describe.Lean(
            DescribeId.Create("circle-double-cover-history-lift"),
            DeclarationHandle.Create(Declaration),
            H("Initial upper data and path history determine the lifted branch"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The public object is Mathlib's canonical liftPath for the squaring "
                        + "covering map. Its lift equation, initial-value computation, and "
                        + "uniqueness characterization are all stated directly.")),
                Paragraph(Text(
                    "A continuous state-only selector would be a global section of the "
                        + "squaring map, which the imported no-section theorem excludes. "
                        + "The path lift remains available because it also receives the "
                        + "initial upper point and the complete base path.")),
                Paragraph(Text(
                    "For the explicit once-around loop based at one, the canonical lift is "
                        + "the half-angle path. It starts at one and ends at minus one, "
                        + "exhibiting the exchange of the two points over the basepoint."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula circle = F.Id("Circle");
        Formula interval = F.Id("I");
        Formula square = F.Id("p");
        Formula covering = F.Id("cov");
        Formula point = F.Id("z");
        Formula basePath = Gamma;
        Formula initial = F.Id("e");
        Formula liftedPath = Seq(Widetilde, Grp(basePath));
        Formula alternative = GammaLower;
        Formula selector = F.Id("s");
        Formula time = F.Id("t");
        Formula loop = Omega;
        Formula liftedLoop = Seq(Widetilde, Grp(loop));
        Formula pathType = Call("ContinuousMap", interval, circle);
        Formula squareType = new Formula.TypeArrow(circle, circle);
        Formula selectorType = new Formula.TypeArrow(circle, circle);
        Formula squareAtPoint = Apply(square, point);
        Formula squareConstruction = Seq(
            Typed(square, squareType), Comma, Sp,
            squareAtPoint, Sp, Eq, Sp,
            point, Caret, Grp(D(2)));
        Formula coveringConstruction = Seq(
            covering, Sp, Eq, Sp,
            Call("isCoveringMap", Call("CircleNpowQuotientCover", D(2))));
        Formula initialCondition = Seq(
            Apply(basePath, D(0)), Sp, Eq, Sp, Apply(square, initial));
        Formula liftedConstruction = Seq(
            liftedPath, Sp, Eq, Sp,
            Call("liftPath", covering, basePath, initial, initialCondition));
        Formula liftEquation = Seq(
            square, Sp, Circ, Sp, liftedPath, Sp, Eq, Sp, basePath);
        Formula liftStarts = Seq(
            Apply(liftedPath, D(0)), Sp, Eq, Sp, initial);
        Formula alternativeConditions = Seq(
            square, Sp, Circ, Sp, alternative, Sp, Eq, Sp, basePath,
            Sp, Land, Sp,
            Apply(alternative, D(0)), Sp, Eq, Sp, initial);
        Formula uniqueness = Seq(
            Forall, Sp, Typed(alternative, pathType), Comma, Sp,
            alternativeConditions, Sp, Rightarrow, Sp,
            alternative, Sp, Eq, Sp, liftedPath);
        Formula canonicalPathClause = Seq(
            Forall, Sp, Typed(basePath, pathType), Comma, Sp,
            Typed(initial, circle), Comma, Sp,
            initialCondition, Comma, Sp,
            F.Id("let"), Sp, liftedConstruction, Semi, Sp,
            liftEquation, Sp, Land, Sp, liftStarts, Sp, Land, Sp, uniqueness);
        Formula noGlobalSelector = Seq(
            Neg, Sp, Exists, Sp, Typed(selector, selectorType), Comma, Sp,
            Call("Continuous", selector), Sp, Land, Sp,
            Forall, Sp, Typed(point, circle), Comma, Sp,
            Apply(square, Apply(selector, point)), Sp, Eq, Sp, point);
        Formula loopConstruction = Seq(
            Typed(loop, pathType), Comma, Sp,
            Forall, Sp, Typed(time, interval), Comma, Sp,
            Apply(loop, time), Sp, Eq, Sp,
            Call("CircleExp", Seq(D(2), Sp, Pi, Sp, time)));
        Formula loopStart = Seq(
            Apply(loop, D(0)), Sp, Eq, Sp, Apply(square, D(1)));
        Formula liftedLoopConstruction = Seq(
            liftedLoop, Sp, Eq, Sp,
            Call("liftPath", covering, loop, D(1), loopStart));
        Formula loopClause = Seq(
            square, Sp, Circ, Sp, liftedLoop, Sp, Eq, Sp, loop,
            Sp, Land, Sp,
            Apply(liftedLoop, D(0)), Sp, Eq, Sp, D(1),
            Sp, Land, Sp,
            Apply(liftedLoop, D(1)), Sp, Eq, Sp, Minus, D(1));

        return Disp(new Formula.Aligned([
            Seq(F.Id("let"), Sp, squareConstruction, Semi),
            Seq(Grp(), F.Id("let"), Sp, coveringConstruction, Semi),
            Seq(Grp(), Open, canonicalPathClause, Close, Sp, Land),
            Seq(Grp(), Open, noGlobalSelector, Close, Sp, Land),
            Seq(Grp(), F.Id("let"), Sp, loopConstruction, Semi),
            Seq(Grp(), F.Id("let"), Sp, liftedLoopConstruction, Semi),
            Seq(Grp(), loopClause, Dot),
        ]));
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

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
