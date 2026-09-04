using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Interpretation;

internal sealed class VisibleSuiteFreshCheckpointDichotomyDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Visible-suite reward optimization and fresh product checkpoints have different "
            + "deployment force.",
        H("Visible-Suite and Fresh-Checkpoint Dichotomy"),
        Blocks(Describe.Lean(
            DescribeId.Create("visible-suite-and-fresh-checkpoint-dichotomy"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/Interpretation/VisibleSuiteFreshCheckpointDichotomy."
                    + "visible_suite_and_fresh_checkpoint_dichotomy"),
            H("Judgment origin separates visible optimization from fresh certification"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A visible-suite program carries the training suite that selected it. Its "
                        + "behavior agrees with the expected output on every observed input and "
                        + "uses a supplied fixed-point-free alternative off that finite image.")),
                Paragraph(Text(
                    "The source objective contains only the number of passed training checks. "
                        + "The lookup program attains every check and therefore maximizes that "
                        + "unregularized reward, while its deployment loss is exactly the mass "
                        + "outside the observed image.")),
                Paragraph(Text(
                    "The canonical lookup compiler identifies this program as the unique program "
                        + "consistent with its suite record. The frozen spectrum-bottom theorem "
                        + "then gives the suite-description bound with fixed overhead.")),
                Paragraph(Text(
                    "A separate implementation is fixed before the checkpoint tuple is sampled. "
                        + "The tuple law is the joint product of the deployment law, so the frozen "
                        + "fresh-checkpoint theorem gives both the exact all-pass mass and its "
                        + "exponential envelope.")),
                Paragraph(Text(
                    "The source's multi-version observations are empirical context and are not "
                        + "asserted as universal theorem clauses."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S0/Computability/DescriptionComplexity/LookupProgramUpperBound")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/ConceptDynamics/Interpretation/FreshIndependentCheckpointGuarantee"))
        ]));

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

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Typeclass(string name, Formula argument) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, argument, Close, CloseBracket);

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(Open, binder, Sp, Mapsto, Sp, body, Close);

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula inputType = F.Id("Input");
        Formula outputType = F.Id("Output");
        Formula deployment = Seq(Mathcal, Grp(F.Id("D")));
        Formula expected = F.Id("xStar");
        Formula opposite = F.Id("opposite");
        Formula budget = F.Id("m");
        Formula trainingSuite = new Formula.Subscript(F.Id("T"), F.Id("train"));
        Formula programCost = F.Id("programCost");
        Formula suiteComplexity = F.Id("suiteComplexity");
        Formula overhead = F.Id("overhead");
        Formula compiler = F.Id("compiler");
        Formula frozen = new Formula.Subscript(F.Id("P"), F.Id("frozen"));
        Formula epsilon = F.Id("epsilon");
        Formula program = F.Id("Q");
        Formula candidate = F.Id("P");
        Formula record = F.Id("Tprime");
        Formula input = F.Id("x");
        Formula output = F.Id("y");
        Formula index = F.Id("j");
        Formula suite = F.Id("T");
        Formula suiteType = Arrow(Call("Fin", budget), inputType);
        Formula implementationType = Arrow(inputType, outputType);
        Formula visibleProgramType = Call("VisibleSuiteProgram", inputType, budget);
        Formula canonicalProgram = Call("VisibleSuiteProgram", trainingSuite);
        Formula coadapted = Call("run", expected, opposite, canonicalProgram);
        Formula consistency = Lambda(
            Seq(program, Colon, Sp, visibleProgramType),
            Lambda(
                Seq(record, Colon, Sp, suiteType),
                Seq(Call("suite", program), Sp, Eq, Sp, record)));
        Formula compilerType = Call(
            "LookupCompiler", suiteType, visibleProgramType, consistency,
            programCost, suiteComplexity, overhead);
        Formula visiblePass = Seq(
            Apply(coadapted, Apply(trainingSuite, index)), Sp, Eq, Sp,
            Apply(expected, Apply(trainingSuite, index)));
        Formula visibleReward = Call("suiteReward", expected, coadapted, trainingSuite);
        Formula candidateReward = Call("suiteReward", expected, candidate, trainingSuite);
        Formula observed = Call("observedInputs", canonicalProgram);
        Formula coadaptedErrorSet = new Formula.SetBuilder(
            Seq(Apply(coadapted, input), Sp, Neq, Sp, Apply(expected, input)),
            input, inputType);
        Formula frozenErrorSet = new Formula.SetBuilder(
            Seq(Apply(frozen, input), Sp, Neq, Sp, Apply(expected, input)),
            input, inputType);
        Formula frozenPassSet = new Formula.SetBuilder(
            Seq(Apply(frozen, input), Sp, Eq, Sp, Apply(expected, input)),
            input, inputType);
        Formula productLaw = Call(
            "pi", Lambda(Seq(index, Colon, Sp, Call("Fin", budget)),
                Call("toMeasure", deployment)));
        Formula allPassSet = new Formula.SetBuilder(
            Seq(Forall, Sp, index, Colon, Sp, Call("Fin", budget), Comma, Sp,
                Apply(frozen, Apply(suite, index)), Sp, Eq, Sp,
                Apply(expected, Apply(suite, index))),
            suite, suiteType);
        Formula freshMass = Call("real", productLaw, allPassSet);
        Formula envelope = Call("exp", Seq(
            Minus, Open, epsilon, Sp, Times, Sp,
            Open, budget, Colon, Sp, real, Close, Close));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, inputType, Comma, Sp, outputType, Colon, Sp, type,
            Comma, RowBreak, Grp(),
            Typeclass("MeasurableSpace", inputType), Comma, Sp,
            Typeclass("MeasurableSingletonClass", inputType), Comma, Sp,
            Typeclass("Countable", inputType), Comma, Sp,
            Typeclass("DecidableEq", inputType), Comma, Sp,
            Typeclass("DecidableEq", outputType), Comma, RowBreak, Grp(),
            Forall, Sp, deployment, Colon, Sp, Call("PMF", inputType), Comma, Sp,
            expected, Colon, Sp, implementationType, Comma, RowBreak, Grp(),
            Forall, Sp, opposite, Colon, Sp, Arrow(outputType, outputType), Comma, Sp,
            Open, Forall, Sp, output, Colon, Sp, outputType, Comma, Sp,
            Apply(opposite, output), Sp, Neq, Sp, output, Close, Comma, RowBreak, Grp(),
            Forall, Sp, budget, Colon, Sp, natural, Comma, Sp,
            trainingSuite, Colon, Sp, suiteType, Comma, RowBreak, Grp(),
            Forall, Sp, programCost, Colon, Sp, Arrow(visibleProgramType, natural),
            Comma, Sp, suiteComplexity, Colon, Sp,
            Arrow(OpenGroup(suiteType), natural), Comma, Sp,
            overhead, Colon, Sp, natural, Comma, RowBreak, Grp(),
            Forall, Sp, compiler, Colon, Sp, compilerType, Comma, RowBreak, Grp(),
            Forall, Sp, frozen, Colon, Sp, implementationType, Comma, Sp,
            epsilon, Colon, Sp, real, Comma, RowBreak, Grp(),
            D(0), Sp, Leq, Sp, epsilon, Sp, Land, Sp,
            epsilon, Sp, Leq, Sp, D(1), Sp, Land, Sp,
            epsilon, Sp, Leq, Sp,
            Call("real", Call("toMeasure", deployment), frozenErrorSet),
            Sp, Rightarrow, RowBreak, Grp(),
            Apply(programCost, canonicalProgram), Sp, Leq, Sp,
            Apply(suiteComplexity, trainingSuite), Sp, Plus, Sp, overhead,
            Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, index, Colon, Sp, Call("Fin", budget), Comma, Sp,
            visiblePass, Close, Sp, Land, RowBreak, Grp(),
            visibleReward, Sp, Eq, Sp, budget, Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, candidate, Colon, Sp, implementationType, Comma, Sp,
            candidateReward, Sp, Leq, Sp, visibleReward, Close,
            Sp, Land, RowBreak, Grp(),
            Call("real", Call("toMeasure", deployment), coadaptedErrorSet),
            Sp, Eq, Sp,
            Call("real", Call("toMeasure", deployment), Call("compl", observed)),
            Sp, Land, RowBreak, Grp(),
            freshMass, Sp, Eq, Sp,
            new Formula.Power(
                Call("real", Call("toMeasure", deployment), frozenPassSet), budget),
            Sp, Land, RowBreak, Grp(),
            freshMass, Sp, Leq, Sp, envelope, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula OpenGroup(Formula value) => Seq(Open, value, Close);
}
