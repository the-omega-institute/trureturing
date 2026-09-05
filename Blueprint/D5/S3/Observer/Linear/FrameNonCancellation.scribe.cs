using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class FrameNonCancellationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Linear/FrameNonCancellation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive frame floor excludes blind modes, while complete tests without a "
            + "uniform floor can still lose control along the infinite tail.",
        H("Frame Non-Cancellation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("attenuated-coordinate-family-tail-escape"),
                DeclarationHandle.Create(
                    Prefix + "attenuated_coordinate_family_tail_escape"),
                H("Complete attenuated coordinates have no uniform lower bound"),
                StatementSource.FromAuthor(TailEscapeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The offline carrier is the real square-summable sequence space. "
                            + "Coordinate n is read with weight one over n plus one, and the "
                            + "analysis energy is the sum of the squared weighted readouts.")),
                    Paragraph(Text(
                        "Every weight is nonzero, so the full coordinate family separates "
                            + "all modes. Its energy is summable and nonnegative. The unit "
                            + "coordinate modes have energy one over n plus one squared, "
                            + "which tends to zero and excludes every positive uniform floor."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("frame-non-cancellation"),
                DeclarationHandle.Create(Prefix + "frame_non_cancellation"),
                H("A positive frame coefficient prevents cancellation"),
                StatementSource.FromAuthor(FrameFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The frame coefficient is definitionally the infimum of the squared "
                            + "analysis-norm ratio over nonzero modes. If this coefficient is "
                            + "positive, an analysis-zero mode cannot be nonzero.")),
                    Paragraph(Text(
                        "The first contrast uses one scalar channel on a real two-coordinate "
                            + "space. Every channel square is nonnegative, but the second "
                            + "coordinate is a nonzero blind mode.")),
                    Paragraph(Text(
                        "The second contrast is the complete attenuated coordinate family. "
                            + "It has infinitely many separating tests and positive square "
                            + "energies, but its unit tail probes force the uniform lower "
                            + "frame coefficient to vanish."))),
                DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Exists(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);

    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = And(clauses[index], result);
        return result;
    }

    private static Formula Lambda(string name, Formula domain, Formula body) =>
        Seq(F.Id(name), Colon, Sp, domain, Sp, Mapsto, Sp, body);

    private static Formula Square(Formula value) =>
        new Formula.Power(value, D(2));

    private static Formula Norm(Formula value) => new Formula.Norm(value);

    private static Formula ReadoutAt(Formula n, Formula d) =>
        Call("attenuatedCoordinateReadout", n, d);

    private static Formula EnergyAt(Formula d) =>
        Call("attenuatedAnalysisEnergy", d);

    private static Formula UnitMode(Formula n) =>
        Call("single", D(2), n, D(1));

    private static Formula TailClauses()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula offline = F.Id("OfflineModeSpace");
        Formula d = F.Id("d");
        Formula n = F.Id("n");
        Formula alpha = Alpha;
        Formula readout = ReadoutAt(n, d);
        Formula readoutSquare = Square(readout);

        Formula complete = ForAll(
            [Bound("d", offline)],
            Implies(
                ForAll([Bound("n", natural)], Equal(readout, D(0))),
                Equal(d, D(0))));
        Formula summable = ForAll(
            [Bound("d", offline)],
            Call("Summable", Lambda("n", natural, readoutSquare)));
        Formula nonnegative = ForAll(
            [Bound("d", offline)],
            AtMost(D(0), EnergyAt(d)));
        Formula tailLimit = Call(
            "Tendsto",
            Lambda("n", natural, EnergyAt(UnitMode(n))),
            F.Id("atTop"),
            Call("nhds", D(0)));
        Formula noUniformFloor = ForAll(
            [Bound("alpha", real)],
            Implies(
                Less(D(0), alpha),
                Exists(
                    [Bound("d", offline)],
                    And(
                        Equal(Norm(d), D(1)),
                        Less(EnergyAt(d), alpha)))));

        return All(complete, summable, nonnegative, tailLimit, noUniformFloor);
    }

    private static Formula TailEscapeFormula() => Disp(TailClauses());

    private static Formula FrameFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula h = F.Id("H");
        Formula k = F.Id("K");
        Formula analysis = F.Id("analysis");
        Formula d = F.Id("d");
        Formula x = F.Id("x");
        Formula channel = F.Id("channel");
        Formula blind = F.Id("blind");
        Formula realPair = Call("Prod", real, real);
        Formula linearMap = Call("LinearMap", real, h, k);
        Formula scalarChannel = Call("LinearMap", real, realPair, real);

        Formula typeclasses = All(
            Call("NormedAddCommGroup", h),
            Call("NormedSpace", real, h),
            Call("NormedAddCommGroup", k),
            Call("NormedSpace", real, k));
        Formula positiveCoefficient = Less(
            D(0), Call("frameLowerCoefficient", analysis));
        Formula noBlindMode = ForAll(
            [Bound("d", h)],
            Implies(
                Equal(Apply(analysis, d), D(0)),
                Equal(d, D(0))));
        Formula singleChannelBlind = Exists(
            [Bound("channel", scalarChannel), Bound("blind", realPair)],
            All(
                NotEqual(blind, D(0)),
                ForAll(
                    [Bound("x", realPair)],
                    AtMost(D(0), Square(Apply(channel, x)))),
                Equal(Apply(channel, blind), D(0))));
        Formula conclusion = All(noBlindMode, singleChannelBlind, TailClauses());

        return Disp(ForAll(
            [Bound("H", type), Bound("K", type), Bound("analysis", linearMap)],
            Implies(All(typeclasses, positiveCoefficient), conclusion)));
    }
}
