using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.LinearMemory;

internal sealed class DualGramConditionNumberDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/LinearMemory/DualGramConditionNumber."
            + "dual_gram_condition_number";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dual Gram operators have one positive-spectrum condition number and paired weak modes.",
        H("Dual Gram Condition Number"),
        Blocks(Describe.Lean(
            DescribeId.Create("dual-gram-condition-number"),
            DeclarationHandle.Create(Declaration),
            H("State and protocol conditioning are dual"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A finite indexed family of scalar readouts constructs the observation map "
                        + "coordinatewise on the square-summable protocol carrier. The positive "
                        + "state and protocol Gram spectra are displayed as literal sets.")),
                Paragraph(Text(
                    "Their supremum-to-infimum ratios agree. For every positive singular value, "
                        + "the observation map and its adjoint transfer nonzero eigenvectors "
                        + "between the state and protocol Gram operators at the same square.")),
                Paragraph(Text(
                    "The proof applies the pinned library's eigenspace and linear-map laws; the "
                        + "observation map is the canonical coordinatewise construction already "
                        + "used by the dual-Gram family."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula scalar = F.Id("K");
        Formula state = F.Id("V");
        Formula index = F.Id("iota");
        Formula readout = F.Id("ell");
        Formula observation = F.Id("M");
        Formula stateSpectrum = F.Id("stateSpectrum");
        Formula protocolSpectrum = F.Id("protocolSpectrum");
        Formula lambda = F.Id("lambda");
        Formula sigma = F.Id("sigma");
        Formula stateVector = F.Id("v");
        Formula protocolVector = F.Id("a");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula indexToScalar = Arrow(index, scalar);
        Formula functional = Call("LinearMap", scalar, state, scalar);
        Formula protocolSpace = Call("PiLp", D(2), indexToScalar);
        Formula observationType = Call("LinearMap", scalar, state, protocolSpace);
        Formula readoutType = Arrow(index, functional);
        Formula adjoint = Call("adjoint", observation);
        Formula stateGram = Call("comp", adjoint, observation);
        Formula protocolGram = Call("comp", observation, adjoint);
        Formula coordinateMap = Call("linearPi", readout);
        Formula l2Equivalence = Call(
            "withLpLinearEquiv", D(2), scalar, indexToScalar);
        Formula observationConstruction = Call(
            "comp", Call("toLinearMap", Call("symm", l2Equivalence)), coordinateMap);
        Formula scalarLambda = Call("ofReal", scalar, lambda);
        Formula sigmaSquare = new Formula.Power(sigma, D(2));
        Formula scalarSigmaSquare = Call("ofReal", scalar, sigmaSquare);
        Formula stateSpectrumBody = And(
            Less(D(0), lambda),
            Call("HasEigenvalue", stateGram, scalarLambda));
        Formula protocolSpectrumBody = And(
            Less(D(0), lambda),
            Call("HasEigenvalue", protocolGram, scalarLambda));
        Formula conditionEquality = Equal(
            new Formula.Fraction(Call("sSup", stateSpectrum), Call("sInf", stateSpectrum)),
            new Formula.Fraction(
                Call("sSup", protocolSpectrum), Call("sInf", protocolSpectrum)));
        Formula stateWitness = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("v", state)],
            Call("HasEigenvector", stateGram, scalarSigmaSquare, stateVector));
        Formula protocolWitness = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("a", protocolSpace)],
            Call("HasEigenvector", protocolGram, scalarSigmaSquare, protocolVector));
        Formula weakModeDuality = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("sigma", real)],
            Implies(Less(D(0), sigma), Iff(stateWitness, protocolWitness)));
        Formula assumptions = And(
            Typeclass("RCLike", scalar),
            And(
                Typeclass("NormedAddCommGroup", state),
                And(
                    Typeclass("InnerProductSpace", scalar, state),
                    And(
                        Typeclass("FiniteDimensional", scalar, state),
                        Typeclass("Fintype", index)))));
        Formula conclusion = Seq(
            Let(observation, observationType, observationConstruction), Sp,
            Let(
                stateSpectrum,
                Call("Set", real),
                new Formula.SetBuilder(stateSpectrumBody, lambda, real)), Sp,
            Let(
                protocolSpectrum,
                Call("Set", real),
                new Formula.SetBuilder(protocolSpectrumBody, lambda, real)), Sp,
            And(conditionEquality, weakModeDuality));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("K", type),
                Bound("V", type),
                Bound("iota", type),
                Bound("ell", readoutType),
            ],
            Implies(assumptions, conclusion)));
    }

    private static Formula Let(Formula name, Formula type, Formula value) =>
        Seq(Operatorname, Grp(F.Id("let")), Sp, name, Colon, Sp, type, Sp,
            Eq, Sp, value, Semi);

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Typeclass(string name, params Formula[] arguments) =>
        Call(name, arguments);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
