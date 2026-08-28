using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.RefinementGeometry;

internal sealed class DynamicIndistinguishabilityCoordinatewiseDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/RefinementGeometry/DynamicIndistinguishabilityCoordinatewise.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dynamic indistinguishability on an independent finite product is exactly "
            + "coordinatewise, and factorwise action is necessary.",
        H("Dynamic Indistinguishability Coordinatewise"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("dynamic-indistinguishability-iff-coordinatewise"),
                DeclarationHandle.Create(
                    Prefix + "dynamic_indistinguishability_iff_coordinatewise"),
                H("Dynamic indistinguishability is coordinatewise"),
                StatementSource.FromAuthor(CoordinatewiseFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For any finite index type and dependent state and output families, "
                            + "the update and readout are formed by applying their local maps "
                            + "at each coordinate.")),
                    Paragraph(Text(
                        "Equality of every global readout at every time implies equality at "
                            + "each coordinate. Conversely, coordinatewise equality at every "
                            + "time gives equality of the dependent output functions by "
                            + "function extensionality.")),
                    Paragraph(Text(
                        "The finite index may be empty; no primality, prime-power, finiteness "
                            + "of carriers, injectivity, surjectivity, or nonconstant readout "
                            + "is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("readout-factorwise-is-necessary"),
                DeclarationHandle.Create(Prefix + "readout_factorwise_is_necessary"),
                H("Factorwise readout is necessary"),
                StatementSource.FromAuthor(ReadoutNecessityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "On a two-coordinate Boolean product, the identity update and "
                            + "constant local readouts make every coordinate pair locally "
                            + "indistinguishable.")),
                    Paragraph(Text(
                        "A cross-coordinate readout that repeats coordinate zero globally "
                            + "separates two such states at time zero. Thus the iff fails when "
                            + "the readout does not act factorwise."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("update-factorwise-is-necessary"),
                DeclarationHandle.Create(Prefix + "update_factorwise_is_necessary"),
                H("Factorwise update is necessary"),
                StatementSource.FromAuthor(UpdateNecessityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "On a two-coordinate product of Boolean pairs, the first-coordinate "
                            + "readout is factorwise and the local updates are identities.")),
                    Paragraph(Text(
                        "A cross-coordinate update copies a hidden second component into the "
                            + "other coordinate. The local relations remain true, but the global "
                            + "relation fails after one step, so factorwise "
                            + "updating is necessary."))),
                DescribeRole.Theorem))));

    private static Formula Named(Formula name) => Seq(Operatorname, Grp(name));

    private static Formula Call(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { Named(function), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }

            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula Naturals() =>
        Seq(Mathbb, Grp(F.Id("N")));

    private static Formula.BoundVariable Bound(string name, Formula type) =>
        new Formula.BoundVariable(FormulaIdentifier.Create(name), type);

    private static Formula ProductState(Formula family) =>
        Call(F.Id("ProductState"), family);

    private static Formula Dynamic(Formula update, Formula readout, Formula left, Formula right) =>
        Call(F.Id("DynamicIndistinguishable"), update, readout, left, right);

    private static Formula FactorwiseUpdate(Formula update) =>
        Call(F.Id("UpdateActsFactorwise"), update);

    private static Formula FactorwiseReadout(Formula readout) =>
        Call(F.Id("ReadoutActsFactorwise"), readout);

    private static Formula CoordinatewiseFormula()
    {
        Formula index = F.Id("k");
        Formula states = F.Id("X");
        Formula outputs = F.Id("O");
        Formula updateFamily = F.Id("F");
        Formula readoutFamily = F.Id("q");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula coordinate = F.Id("i");
        Formula fin = Call(F.Id("Fin"), index);
        Formula familyType = Arrow(fin, TypeUniverse());
        Formula stateProduct = ProductState(states);
        Formula updateType = Seq(
            Pi, Sp, coordinate, Colon, fin, Comma, Sp,
            Arrow(Apply(states, coordinate), Apply(states, coordinate)));
        Formula readoutType = Seq(
            Pi, Sp, coordinate, Colon, fin, Comma, Sp,
            Arrow(Apply(states, coordinate), Apply(outputs, coordinate)));
        Formula update = Call(F.Id("coordinateUpdate"), updateFamily);
        Formula readout = Call(F.Id("coordinateReadout"), readoutFamily);
        Formula global = Dynamic(update, readout, left, right);
        Formula local = Dynamic(
            Apply(updateFamily, coordinate),
            Apply(readoutFamily, coordinate),
            Apply(left, coordinate),
            Apply(right, coordinate));
        Formula body = Iff(
            global,
            new Formula.BindMany(
                FormulaQuantifier.ForAll,
                [Bound("i", fin)],
                local));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("k", Naturals()),
                Bound("X", familyType),
                Bound("O", familyType),
                Bound("F", updateType),
                Bound("q", readoutType),
                Bound("x", stateProduct),
                Bound("y", stateProduct),
            ],
            body));
    }

    private static Formula ReadoutNecessityFormula()
    {
        Formula identity = F.Id("id");
        Formula crossReadout = F.Id("crossBooleanReadout");
        Formula localRelation = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", Call(F.Id("Fin"), D(2)))],
            Dynamic(identity, F.Id("constantFalse"),
                F.Id("booleanStateAi"), F.Id("booleanStateBi")));
        Formula global = Dynamic(identity, crossReadout,
            F.Id("booleanStateA"), F.Id("booleanStateB"));

        return Disp(And(
            FactorwiseUpdate(identity),
            And(
                new Formula.Not(FactorwiseReadout(crossReadout)),
                new Formula.Not(Iff(global, localRelation)))));
    }

    private static Formula UpdateNecessityFormula()
    {
        Formula readout = F.Id("firstCoordinateReadout");
        Formula update = F.Id("hiddenCrossUpdate");
        Formula localRelation = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", Call(F.Id("Fin"), D(2)))],
            Dynamic(F.Id("id"), F.Id("first"),
                F.Id("hiddenStateAi"), F.Id("hiddenStateBi")));
        Formula global = Dynamic(update, readout,
            F.Id("hiddenStateA"), F.Id("hiddenStateB"));

        return Disp(And(
            FactorwiseReadout(readout),
            And(
                new Formula.Not(FactorwiseUpdate(update)),
                new Formula.Not(Iff(global, localRelation)))));
    }
}
