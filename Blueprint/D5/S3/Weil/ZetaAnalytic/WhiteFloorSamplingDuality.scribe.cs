using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaAnalytic;

internal sealed class WhiteFloorSamplingDualityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/ZetaAnalytic/WhiteFloorSamplingDuality.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A spectral quadratic identity identifies the local white floor with the least "
            + "unit-norm sampling energy.",
        H("White Floor and Sampling Duality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("white-floor-equals-least-sampling-bound"),
                DeclarationHandle.Create(Prefix + "white_floor_sampling_frame_duality"),
                H("White floor equals the least sampling bound"),
                StatementSource.FromAuthor(DualityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The cone-margin theorem first expresses the floor as a nonzero "
                        + "Rayleigh infimum. Normalizing each nonzero test vector proves "
                        + "that this value set is exactly the unit-sphere sampling set."))),
                DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Apply(Formula function, Formula value) =>
        Call("apply", function, value);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Square(Formula value) => new Formula.Power(Seq(value), D(2));

    private static Formula Norm(Formula value) => new Formula.Norm(value);

    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = And(clauses[index], result);
        return result;
    }

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Exists(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);

    private static Formula DualityFormula()
    {
        Formula type = F.Id("Type"), real = Call("Real");
        Formula source = F.Id("H"), target = F.Id("K");
        Formula quadratic = F.Id("quadratic"), sampling = F.Id("sampling");
        Formula f = F.Id("f"), lambda = F.Id("lambda"), r = F.Id("r");
        Formula whiteFloors = F.Id("whiteFloors");
        Formula samplingBounds = F.Id("samplingBounds");
        Formula sampleEnergy = Square(Norm(Apply(sampling, f)));
        Formula sourceNormSq = Square(Norm(f));
        Formula spectralIdentity = ForAll(
            [Bound("f", source)],
            Equal(Apply(quadratic, f), sampleEnergy));
        Formula floorPredicate = ForAll(
            [Bound("f", source)],
            AtMost(D(0), Call("sub", Apply(quadratic, f),
                Call("mul", lambda, sourceNormSq))));
        Formula unitSamplingPredicate = Exists(
            [Bound("f", source)],
            And(Equal(Norm(f), D(1)), Equal(r, sampleEnergy)));
        Formula whiteFloorSet = new Formula.SetBuilder(floorPredicate, lambda, real);
        Formula samplingBoundSet =
            new Formula.SetBuilder(unitSamplingPredicate, r, real);
        Formula conclusion = Seq(
            Operatorname, Grp(F.Id("let")), Sp, whiteFloors, Sp, Eq, Sp,
            whiteFloorSet, Comma, Sp,
            Operatorname, Grp(F.Id("let")), Sp, samplingBounds, Sp, Eq, Sp,
            samplingBoundSet, Comma, Sp,
            Equal(Call("sSup", whiteFloors), Call("sInf", samplingBounds)));
        Formula assumptions = All(
            Call("NormedAddCommGroup", source),
            Call("NormedSpace", real, source),
            Call("Nontrivial", source),
            Call("NormedAddCommGroup", target),
            Call("NormedSpace", real, target),
            spectralIdentity);

        return F.Disp(ForAll(
            [
                Bound("H", type),
                Bound("K", type),
                Bound("quadratic", new Formula.TypeArrow(source, real)),
                Bound("sampling", Call("ContinuousLinearMap", real, source, target)),
            ],
            Implies(assumptions, conclusion)));
    }
}
