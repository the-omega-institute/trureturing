using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Completion;

internal sealed class CompatibleUnboundedCoordinatesDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Quantum/Completion/CompatibleUnboundedCoordinates.";
    private static Formula K => F.Id("K");
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula n => F.Id("n");
    private static Formula i => F.Id("i");
    private static Formula x => F.Id("x");
    private static Formula Ambient => Call("lp", Fn(i, N, K), D(2));
    private static Formula Stages => Fn(n, N, Stage(n));
    private static Formula Norms => Fn(n, N, Norm(Ones(n)));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual first-coordinate projections are compatible but the partial-one family is unbounded and unrealizable.",
        H("Compatible Unbounded Coordinates"),
        Blocks(
            Entry("coordinate-space", "coordinateSpace", "The actual first-coordinate span",
                All(n, N, Equal(Seq(Stage(n), Colon, Sp, Call("Submodule", K, Ambient)), Call("span", K,
                    Call("range", Fn(i, Call("Fin", n), Single(Call("val", i), D(1))))))),
                "Coordinates are numbered from zero. The range n consists of exactly the first n "
                    + "coordinates, and stage zero is the span of the empty set.", DescribeRole.Definition),
            Entry("partial-ones", "partialOnes", "The actual partial-one vectors",
                All(n, N, Equal(Seq(Ones(n), Colon, Sp, Ambient), CoordinateSum(n, D(1)))),
                "These are finite sums in the existing lp space at exponent 2, with its existing "
                    + "norm and inner product.", DescribeRole.Definition),
            Entry("finite-dimensional-stages", "coordinateSpaceFiniteDimensional",
                "Finite-dimensional coordinate stages",
                All(n, N, Call("FiniteDimensional", K, Stage(n))),
                "The finite range of standard coordinate vectors spans each stage.", DescribeRole.Proposition),
            Entry("actual-orthogonal-projections", "coordinateSpaceHasOrthogonalProjection",
                "Actual orthogonal projections",
                All(n, N, Call("HasOrthogonalProjection", Stage(n))),
                "Finite dimensionality supplies completeness locally, so no stage-completeness "
                    + "hypothesis is added.", DescribeRole.Proposition),
            Entry("coordinate-projection", "coordinate_projection", "Projection is coordinate truncation",
                All(n, N, All(x, Ambient,
                    Equal(Project(n, x), CoordinateSum(n, Apply(x, i))))),
                "The finite sum lies in the independently defined span. Its residual has zero "
                    + "first-n coordinates, so projection uniqueness applies. Mathlib's complex "
                    + "inner product is conjugate linear in the first argument; the proof uses "
                    + "the residual in that argument and the coordinate vector in the second.",
                DescribeRole.Theorem),
            Entry("compatible-unbounded-coordinates", "compatible_unbounded_coordinates",
                "Compatible coordinates without a Hilbert-space realization", CompleteFormula(),
                "All earlier-stage projection equations hold, while the norms tend to infinity. "
                    + "Projection contraction excludes a common lp preimage. Actual lp vectors "
                    + "have summable squared coordinate norms, whereas constant-one coefficients "
                    + "do not. The final exclusion concerns the existing submodule of bounded "
                    + "functions; compatibility alone does not supply boundedness.", DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string declaration, string title,
        Formula formula, string narrative, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Gid + declaration), H(title),
            StatementSource.FromAuthor(Disp(Seq(
                Begin, Grp(F.Id("gathered")),
                Forall, Sp, K, Colon, Sp, F.Id("Type"), Sp, F.Id("u"), Comma, Sp,
                OpenBracket, Call("RCLike", K), CloseBracket, Comma, RowBreak, Grp(),
                formula, Dot, End, Grp(F.Id("gathered"))))),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text(narrative))), role);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Apply(Formula function, Formula argument) => Seq(function, Open, argument, Close);
    private static Formula Par(Formula body) => Seq(Open, body, Close);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, variable, Colon, Sp, type, Comma, Sp, body);
    private static Formula Fn(Formula variable, Formula type, Formula body) =>
        Par(Seq(variable, Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Square(Formula value) => Seq(value, Caret, Grp(D(2)));
    private static Formula Norm(Formula value) => Seq(Vert, Sp, value, Vert);
    private static Formula Stage(Formula index) => Call("coordinateSpace", K, index);
    private static Formula Ones(Formula index) => Call("partialOnes", K, index);
    private static Formula Project(Formula index, Formula vector) => Call("starProjection", Stage(index), vector);
    private static Formula Single(Formula index, Formula value) => Call("single", D(2), index, value);
    private static Formula CoordinateSum(Formula length, Formula coefficient) =>
        Seq(Sum, Underscore, Grp(i, Sp, InMacro, Sp, Call("range", length)), Sp, Single(i, coefficient));
    private static Formula NotExists(Formula variable, Formula type, Formula body) =>
        Seq(Neg, Par(Seq(Exists, Sp, variable, Colon, Sp, type, Comma, Sp, body)));

    private static Formula CompleteFormula()
    {
        Formula m = F.Id("m");
        Formula z = F.Id("z");
        Formula bounds = Seq(
            Norm(Project(n, x)), Sp, Le, Sp, Norm(x), Sp, Land, Sp,
            Square(Norm(Project(n, x))), Sp, Le, Sp, Square(Norm(x)));
        Formula constantSquares = Fn(i, N, Square(Norm(Seq(Open, D(1), Colon, Sp, K, Close))));
        Formula boundedFunctions = Call("BoundedContinuousFunction", N, Ambient);
        Formula[] clauses = [
            Call("Monotone", Stages),
            All(n, N, Seq(Ones(n), Sp, InMacro, Sp, Stage(n))),
            All(n, N, All(i, N, Equal(Apply(Ones(n), i),
                Call("ite", Seq(i, Sp, Lt, Sp, n), D(1), D(0))))),
            All(m, N, All(n, N, Seq(m, Sp, Le, Sp, n, Sp, Implies, Sp,
                Equal(Project(m, Ones(n)), Ones(m))))),
            All(n, N, Equal(Square(Norm(Ones(n))), Seq(Open, n, Colon, Sp, R, Close))),
            All(n, N, Equal(Norm(Ones(n)), Seq(Sqrt, Grp(n)))),
            Call("Tendsto", Norms, Call("atTop"), Call("atTop")),
            Seq(Neg, Call("BddAbove", Call("range", Norms))),
            All(x, Ambient, All(n, N, Par(bounds))),
            NotExists(x, Ambient, All(n, N, Equal(Project(n, x), Ones(n)))),
            All(x, Ambient, Call("Summable", Fn(i, N, Square(Norm(Apply(x, i)))))),
            Seq(Neg, Call("Summable", constantSquares)),
            Seq(Neg, Operatorname, Grp(F.Id("Mem"), Ell, Sp, F.Id("p")), Open,
                Fn(i, N, Seq(Open, D(1), Colon, Sp, K, Close)), Comma, Sp, D(2), Close),
            NotExists(z, Call("boundedInverseLimit", Stages),
                All(n, N, Equal(Apply(Seq(Open, z, Colon, Sp, boundedFunctions, Close), n), Ones(n))))
        ];
        var items = new List<Formula>();
        for (var index = 0; index < clauses.Length; index++)
        {
            if (index > 0) items.AddRange([Sp, Land, RowBreak, Grp()]);
            items.Add(Par(clauses[index]));
        }
        return Seq([.. items]);
    }
}
