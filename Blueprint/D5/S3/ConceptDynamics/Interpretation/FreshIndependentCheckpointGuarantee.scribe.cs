using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Interpretation;

internal sealed class FreshIndependentCheckpointGuaranteeDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fresh checkpoints governed by the deployment product law certify a frozen implementation.",
        H("Fresh Independent Checkpoint Guarantee"),
        Blocks(Describe.Lean(
            DescribeId.Create("fresh-independent-checkpoint-deployment-guarantee"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/Interpretation/FreshIndependentCheckpointGuarantee."
                    + "fresh_independent_checkpoint_deployment_guarantee"),
            H("Fresh deployment checkpoints give an exponential all-pass guarantee"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let deployment be an arbitrary probability mass function on a countable "
                        + "measurable input carrier. The implementation and expected behavior are "
                        + "fixed before the suite law is constructed.")),
                Paragraph(Text(
                    "The checkpoint tuple is governed by the finite product measure of copies of "
                        + "deployment. This joint law is the independence premise; it is not "
                        + "represented by a family of matching marginal assertions.")),
                Paragraph(Text(
                    "The exact all-pass mass is the single-check pass mass raised to the suite "
                        + "budget. If deployment loss is at least epsilon, that mass is at most "
                        + "(1 - epsilon)^m and hence at most exp(-epsilon m).")),
                Paragraph(Text(
                    "Pinned Mathlib supplies Measure.pi_pi, ENNReal.toReal_prod, and the real "
                        + "probability-complement identity. The frozen repository theorem "
                        + "independent_sampling_exponential_bound supplies the final step directly. "
                        + "The existing interpretation witnesses are Boolean special cases and do "
                        + "not state this arbitrary frozen-implementation guarantee."))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S3/TotalVariation/IndependentSamplingExponentialBound"))]));

    private static Formula Typeclass(string name, Formula argument) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, argument, Close, CloseBracket);

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

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula inputType = F.Id("Input"), outputType = F.Id("Output");
        Formula deployment = Seq(Mathcal, Grp(F.Id("D")));
        Formula implementation = F.Id("P"), expected = F.Id("xStar");
        Formula budget = F.Id("m"), epsilon = F.Id("epsilon");
        Formula input = F.Id("x"), suite = F.Id("suite"), index = F.Id("j");
        Formula suiteType = Seq(Call("Fin", budget), Sp, To, Sp, inputType);
        Formula implementationType = Seq(inputType, Sp, To, Sp, outputType);
        Formula implementationAtInput = Apply(implementation, input);
        Formula expectedAtInput = Apply(expected, input);
        Formula passSet = new Formula.SetBuilder(
            Seq(implementationAtInput, Sp, Eq, Sp, expectedAtInput),
            input,
            inputType);
        Formula failureSet = new Formula.SetBuilder(
            Seq(implementationAtInput, Sp, Neq, Sp, expectedAtInput),
            input,
            inputType);
        Formula suiteLaw = new Formula.Subscript(F.Id("mu"), F.Id("suite"));
        Formula suiteLawDefinition = Seq(
            suiteLaw, Colon, Sp, Call("Measure", suiteType), Sp, Eq, Sp,
            Call("pi", Seq(index, Sp, Mapsto, Sp, Call("toMeasure", deployment))));
        Formula allPass = F.Id("Apass");
        Formula allPassBody = Seq(
            Forall, Sp, index, Colon, Sp, Call("Fin", budget), Comma, Sp,
            Apply(implementation, Apply(suite, index)), Sp, Eq, Sp,
            Apply(expected, Apply(suite, index)));
        Formula allPassSet = new Formula.SetBuilder(allPassBody, suite, suiteType);
        Formula allPassDefinition = Seq(
            allPass, Colon, Sp, Call("Set", suiteType), Sp, Eq, Sp, allPassSet);
        Formula allPassMass = Call("real", suiteLaw, allPass);
        Formula passMass = Call("real", Call("toMeasure", deployment), passSet);
        Formula loss = Call("real", Call("toMeasure", deployment), failureSet);
        Formula exactMass = new Formula.Power(passMass, Seq(budget));
        Formula envelope = Call("exp", Seq(
            Minus, Open, epsilon, Sp, Times, Sp,
            Open, budget, Colon, Sp, reals, Close, Close));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, inputType, Comma, Sp, outputType, Colon, Sp, type,
            Comma, RowBreak, Grp(),
            Typeclass("MeasurableSpace", inputType), Comma, Sp,
            Typeclass("MeasurableSingletonClass", inputType), Comma, Sp,
            Typeclass("Countable", inputType), Comma, RowBreak, Grp(),
            Forall, Sp, deployment, Colon, Sp, Call("PMF", inputType), Comma, Sp,
            implementation, Comma, Sp, expected, Colon, Sp, implementationType,
            Comma, RowBreak, Grp(),
            Forall, Sp, budget, Colon, Sp, naturals, Comma, Sp,
            epsilon, Colon, Sp, reals, Comma, RowBreak, Grp(),
            D(0), Sp, Leq, Sp, epsilon, Sp, Land, Sp,
            epsilon, Sp, Leq, Sp, D(1), Sp, Land, Sp,
            epsilon, Sp, Leq, Sp, loss, Sp, Rightarrow, RowBreak, Grp(),
            Operatorname, Grp(F.Id("let")), Open,
            suiteLawDefinition, Comma, RowBreak, Grp(),
            allPassDefinition, Close, Semi, RowBreak, Grp(),
            allPassMass, Sp, Eq, Sp, exactMass,
            Sp, Land, Sp, RowBreak, Grp(),
            allPassMass, Sp, Leq, Sp, envelope, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
