using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.BlockStructure;

internal sealed class CommonSpectrumMasterFeasibilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite common-spectrum feasibility is exactly one positive Hermitian Toeplitz "
            + "moment system, with a real-coordinate reduction on the even branch.",
        H("Common-Spectrum Master Feasibility"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-common-spectrum-master-feasibility"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/BlockStructure/CommonSpectrumMasterFeasibility."
                        + "common_spectrum_master_feasibility"),
                H("One Toeplitz system carries every finite observation"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The positive-spectrum side is carried by an actual finite positive "
                            + "measure on the circle. Each supplied linear observation acts on "
                            + "the same truncated Toeplitz moment matrix.")),
                    Paragraph(Text(
                        "The reverse implication applies the frozen finite Toeplitz moment "
                            + "representation theorem after extending the supplied Hermitian "
                            + "window by zero outside its stated depth.")),
                    Paragraph(Text(
                        "A Hermitian window is uniquely encoded by one real center and its "
                            + "positive complex moments, giving 2(N+1)-1 real coordinates. "
                            + "The real even branch is uniquely encoded by N+1 real values."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula integers = Seq(Mathbb, Grp(F.Id("Z")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula type = F.Id("Type");
        Formula circle = F.Id("Circle");
        Formula depth = F.Id("N");
        Formula observer = F.Id("S");
        Formula output = F.Id("O");
        Formula observation = F.Id("L");
        Formula admissible = F.Id("I");
        Formula moment = F.Id("y");
        Formula measure = F.Id("mu");
        Formula index = F.Id("k");
        Formula observationIndex = F.Id("s");
        Formula coordinate = F.Id("x");

        Formula matrixIndex = Call("Fin", Seq(depth, Sp, Plus, Sp, D(1)));
        Formula matrixType = Call("Matrix", matrixIndex, matrixIndex, complex);
        Formula observationType = Arrow(
            observer, Call("LinearMap", real, matrixType, output));
        Formula admissibleType = Arrow(observer, Call("Set", output));
        Formula momentType = Arrow(integers, complex);
        Formula finiteMeasure = Call("FiniteMeasure", circle);
        Formula generalCount = Seq(
            D(2), Sp, Cdot, Sp, Open, depth, Sp, Plus, Sp, D(1), Close,
            Sp, Minus, Sp, D(1));
        Formula generalCoordinateType = Arrow(Call("Fin", generalCount), real);
        Formula evenCoordinateType = Arrow(
            Call("Fin", Seq(depth, Sp, Plus, Sp, D(1))), real);

        Formula measureMatrix = Toeplitz(Call("circleMoment", measure));
        Formula momentMatrix = Toeplitz(moment);
        Formula bounded = Seq(Call("natAbs", index), Sp, Le, Sp, depth);
        Formula negativeIndex = Grp(Minus, index);
        Formula hermitian = ForAllWhere(
            "k", integers, bounded,
            Seq(Apply(moment, negativeIndex), Sp, Eq, Sp,
                StarOf(Apply(moment, index))));
        Formula evenMoment = ForAllWhere(
            "k", integers, bounded,
            Seq(Apply(moment, negativeIndex), Sp, Eq, Sp, Apply(moment, index)));
        Formula measureInvariant = Seq(
            Call("map", measure, F.Id("inv")), Sp, Eq, Sp, measure);
        Formula measureConstraints = ForAllObservation(measureMatrix);
        Formula momentConstraints = ForAllObservation(momentMatrix);
        Formula positive = Call("PosSemidef", momentMatrix);
        Formula generalCoordinates = UniqueCoordinates(
            generalCoordinateType, "hermitianMomentCoordinates");
        Formula evenCoordinates = UniqueCoordinates(
            evenCoordinateType, "realEvenMomentCoordinates");

        Formula generalMeasureFeasible = ExistsMany(
            [Bound("mu", finiteMeasure)], measureConstraints);
        Formula generalMomentFeasible = ExistsMany(
            [Bound("y", momentType)],
            And(positive, hermitian, momentConstraints, generalCoordinates));
        Formula evenMeasureFeasible = ExistsMany(
            [Bound("mu", finiteMeasure)], And(measureInvariant, measureConstraints));
        Formula evenMomentFeasible = ExistsMany(
            [Bound("y", momentType)],
            And(positive, hermitian, evenMoment, momentConstraints, evenCoordinates));
        Formula generalEquivalence = new Formula.Logic(
            generalMeasureFeasible, FormulaLogicOperator.Iff, generalMomentFeasible);
        Formula evenEquivalence = new Formula.Logic(
            evenMeasureFeasible, FormulaLogicOperator.Iff, evenMomentFeasible);
        Formula conclusion = new Formula.Logic(
            generalEquivalence, FormulaLogicOperator.And, evenEquivalence);
        Formula instancePremises = new Formula.Logic(
            Call("AddCommMonoid", output), FormulaLogicOperator.And,
            Call("Module", real, output));
        Formula scopedConclusion = new Formula.Logic(
            instancePremises, FormulaLogicOperator.Implies, conclusion);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("N", natural),
                Bound("S", type),
                Bound("O", type),
                Bound("L", observationType),
                Bound("I", admissibleType),
            ],
            scopedConclusion));

        Formula Toeplitz(Formula sequence) => Call("toeplitzMatrix", sequence, depth);

        Formula ForAllObservation(Formula matrix) => new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", observer)],
            Seq(Apply(Apply(observation, observationIndex), matrix), Sp, InMacro, Sp,
                Apply(admissible, observationIndex)));

        Formula UniqueCoordinates(Formula coordinateType, string decoder) => Seq(
            Exists, Bang, Sp, Typed(coordinate, coordinateType), Comma, Sp,
            ForAllWhere(
                "k", integers, bounded,
                Seq(Call(decoder, depth, coordinate, index), Sp, Eq, Sp,
                    Apply(moment, index))));
    }

    private static Formula ForAllWhere(
        string variable, Formula type, Formula premise, Formula conclusion) =>
        new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound(variable, type)],
            Seq(premise, Sp, Rightarrow, Sp, conclusion));

    private static Formula And(params Formula[] clauses)
    {
        Formula result = clauses[0];
        for (var index = 1; index < clauses.Length; index++)
        {
            result = new Formula.Logic(result, FormulaLogicOperator.And, clauses[index]);
        }

        return result;
    }

    private static Formula ExistsMany(
        IReadOnlyList<Formula.BoundVariable> variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

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

    private static Formula StarOf(Formula value) =>
        Seq(Grp(value), Caret, Grp(Star));

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);
}
