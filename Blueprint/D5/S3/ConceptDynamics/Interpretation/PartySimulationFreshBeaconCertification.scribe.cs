using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Interpretation;

internal sealed class PartySimulationFreshBeaconCertificationDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Interpretation/PartySimulationFreshBeaconCertification.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Party-simulable certificates have bounded approval, while a fresh beacon gives a "
            + "product-law guarantee with an explicit total-variation charge.",
        H("Party Simulation and Fresh-Beacon Certification"),
        Blocks(Describe.Lean(
            DescribeId.Create("party-simulation-and-fresh-beacon-certification"),
            DeclarationHandle.Create(
                DeclarationPrefix + "party_simulation_and_fresh_beacon_certification"),
            H("Simulation necessity and fresh-beacon sufficiency"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The first implication quantifies over every seed-indexed implementation. "
                        + "The certificate depends only on the party seed, and the co-selected "
                        + "bad implementation agrees with expected behavior on that same suite.")),
                Paragraph(Text(
                    "Reliability therefore applies to a verifier input identical to the honest "
                        + "all-green input. Approval of the fixed nontrivial tier has probability "
                        + "at most delta, and total Boolean output makes the trivial tier its "
                        + "probability complement.")),
                Paragraph(Text(
                    "The second implication fixes the implementation before the anchor. Task and "
                        + "anchor are governed by their product measure, the public suite map "
                        + "pushes the anchor law forward, and the ideal suite is the finite product "
                        + "of the deployment law.")),
                Paragraph(Text(
                    "The exact independent all-pass bound is transported to the induced suite law "
                        + "through the finite event characterization of total variation. Every "
                        + "carrier instance, probability law, map, predicate, and threshold premise "
                        + "is displayed explicitly in the proposition."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/ConceptDynamics/Interpretation/FreshIndependentCheckpointGuarantee")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/TotalVariation/Metric")),
        ]));

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

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Product(Formula left, Formula right) =>
        Seq(Open, left, Close, Sp, Times, Sp, Open, right, Close);

    private static Formula Pair(Formula left, Formula right) =>
        Seq(Open, left, Comma, Sp, right, Close);

    private static Formula Field(Formula value, byte field) =>
        Seq(value, Dot, D(field));

    private static Formula Lambda(Formula variable, Formula body) =>
        Seq(Open, variable, Sp, Mapsto, Sp, body, Close);

    private static Formula Singleton(Formula value) =>
        Seq(OpenBrace, value, CloseBrace);

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula boolType = F.Id("Bool");
        Formula seed = F.Id("Seed"), coin = F.Id("VerifierCoin");
        Formula input = F.Id("Input"), output = F.Id("Output");
        Formula certificateType = F.Id("Certificate");
        Formula anchor = F.Id("Anchor"), task = F.Id("Task");
        Formula deployment = F.Id("deployment"), expected = F.Id("expected");
        Formula budget = F.Id("m"), epsilon = F.Id("epsilon"), delta = F.Id("delta");
        Formula seedLaw = F.Id("seedLaw"), coinLaw = F.Id("verifierCoinLaw");
        Formula partySuite = F.Id("partySuite"), certificate = F.Id("certificate");
        Formula verifier = F.Id("verifier"), coSelected = F.Id("coSelected");
        Formula taskLaw = F.Id("taskLaw"), anchorLaw = F.Id("anchorLaw");
        Formula suiteMap = F.Id("suiteMap"), implementation = F.Id("implementation");
        Formula strategy = F.Id("strategy"), omega = F.Id("omega");
        Formula seedValue = F.Id("s"), indexValue = F.Id("i");
        Formula sample = F.Id("x"), suite = F.Id("u"), taskAnchor = F.Id("z");

        Formula finBudget = Call("Fin", budget);
        Formula suiteType = Arrow(finBudget, input);
        Formula behaviorType = Arrow(input, output);
        Formula strategyType = Arrow(seed, behaviorType);
        Formula recordType = Arrow(finBudget, Product(input, output));
        Formula partyWorld = Product(seed, coin);
        Formula beaconWorld = Product(task, anchor);
        Formula verifierType = Arrow(
            Product(recordType, certificateType), Arrow(coin, boolType));

        Formula loss = F.Id("L");
        Formula behavior = F.Id("P");
        Formula lossDefinition = Seq(
            loss, Colon, Sp, Arrow(Seq(Open, behaviorType, Close), reals), Sp, Eq, Sp,
            Lambda(behavior, Call("real", Call("toMeasure", deployment),
                new Formula.SetBuilder(
                    Seq(Apply(behavior, sample), Sp, Neq, Sp, Apply(expected, sample)),
                    sample, input))));

        Formula partyJoint = F.Id("nuParty");
        Formula partyJointDefinition = Seq(
            partyJoint, Colon, Sp, Call("Measure", partyWorld), Sp, Eq, Sp,
            Call("prod", Call("toMeasure", seedLaw), Call("toMeasure", coinLaw)));

        Formula beaconJoint = F.Id("nuBeacon");
        Formula beaconJointDefinition = Seq(
            beaconJoint, Colon, Sp, Call("Measure", beaconWorld), Sp, Eq, Sp,
            Call("prod", Call("toMeasure", taskLaw), Call("toMeasure", anchorLaw)));

        Formula partyRecord = F.Id("partyRecord");
        Formula recordAt = Pair(
            Apply(partySuite, seedValue, indexValue),
            Apply(strategy, seedValue, Apply(partySuite, seedValue, indexValue)));
        Formula partyRecordDefinition = Seq(
            partyRecord, Colon, Sp,
            Arrow(Seq(Open, strategyType, Close), Arrow(seed, recordType)), Sp, Eq, Sp,
            Lambda(strategy, Lambda(seedValue, Lambda(indexValue, recordAt))));

        Formula honestRecord = F.Id("honestRecord");
        Formula honestRecordAt = Pair(
            Apply(partySuite, seedValue, indexValue),
            Apply(expected, Apply(partySuite, seedValue, indexValue)));
        Formula honestRecordDefinition = Seq(
            honestRecord, Colon, Sp, Arrow(seed, recordType), Sp, Eq, Sp,
            Lambda(seedValue, Lambda(indexValue, honestRecordAt)));

        Formula inducedLaw = F.Id("muInduced");
        Formula inducedLawDefinition = Seq(
            inducedLaw, Colon, Sp, Call("Measure", suiteType), Sp, Eq, Sp,
            Call("map", suiteMap, Call("toMeasure", anchorLaw)));

        Formula idealLaw = F.Id("muIdeal");
        Formula idealLawDefinition = Seq(
            idealLaw, Colon, Sp, Call("Measure", suiteType), Sp, Eq, Sp,
            Call("pi", Lambda(indexValue, Call("toMeasure", deployment))));

        Formula omegaSeed = Field(omega, 1), omegaCoin = Field(omega, 2);
        Formula strategyAtSeed = Apply(strategy, omegaSeed);
        Formula verifierStrategyInput = Pair(
            Apply(partyRecord, strategy, omegaSeed), Apply(certificate, omegaSeed));
        Formula reliabilityEvent = new Formula.SetBuilder(
            Seq(
                Apply(verifier, verifierStrategyInput, omegaCoin), Sp, Eq, Sp,
                F.Id("true"), Sp, Land, Sp,
                epsilon, Sp, Lt, Sp, Apply(loss, strategyAtSeed)),
            omega, partyWorld);
        Formula reliability = Seq(
            Forall, Sp, strategy, Colon, Sp, strategyType, Comma, Sp,
            Call("real", partyJoint, reliabilityEvent), Sp, Leq, Sp, delta);

        Formula suiteInput = Apply(partySuite, seedValue, indexValue);
        Formula coSelectedPasses = Seq(
            Forall, Sp, seedValue, Colon, Sp, seed, Comma, Sp,
            indexValue, Colon, Sp, finBudget, Comma, Sp,
            Apply(coSelected, seedValue, suiteInput), Sp, Eq, Sp,
            Apply(expected, suiteInput));
        Formula coSelectedBad = Seq(
            Forall, Sp, seedValue, Colon, Sp, seed, Comma, Sp,
            epsilon, Sp, Lt, Sp, Apply(loss, Apply(coSelected, seedValue)));

        Formula verifierHonestInput = Pair(
            Apply(honestRecord, omegaSeed), Apply(certificate, omegaSeed));
        Formula honestGrant = new Formula.SetBuilder(
            Seq(Apply(verifier, verifierHonestInput, omegaCoin), Sp, Eq, Sp,
                F.Id("true")),
            omega, partyWorld);
        Formula trivialTier = new Formula.SetBuilder(
            Seq(Apply(verifier, verifierHonestInput, omegaCoin), Sp, Eq, Sp,
                F.Id("false")),
            omega, partyWorld);
        Formula necessityConclusion = Seq(
            Call("real", partyJoint, honestGrant), Sp, Leq, Sp, delta,
            Sp, Land, Sp,
            D(1), Sp, Minus, Sp, delta, Sp, Leq, Sp,
            Call("real", partyJoint, trivialTier));
        Formula necessity = Seq(
            Open, Open, reliability, Close, Sp, Rightarrow, RowBreak, Grp(),
            Open, coSelectedPasses, Close, Sp, Rightarrow, RowBreak, Grp(),
            Open, coSelectedBad, Close, Sp, Rightarrow, RowBreak, Grp(),
            necessityConclusion, Close);

        Formula implementationLoss = Apply(loss, implementation);
        Formula taskAnchorValue = Field(taskAnchor, 2);
        Formula anchoredInput = Apply(suiteMap, taskAnchorValue, indexValue);
        Formula beaconPassEvent = new Formula.SetBuilder(
            Seq(
                Forall, Sp, indexValue, Colon, Sp, finBudget, Comma, Sp,
                Apply(implementation, anchoredInput), Sp, Eq, Sp,
                Apply(expected, anchoredInput)),
            taskAnchor, beaconWorld);
        Formula inducedMass = Lambda(
            suite, Call("real", inducedLaw, Singleton(suite)));
        Formula idealMass = Lambda(
            suite, Call("real", idealLaw, Singleton(suite)));
        Formula powerBound = new Formula.Power(
            Seq(Open, D(1), Sp, Minus, Sp, epsilon, Close), Seq(budget));
        Formula sufficiencyConclusion = Seq(
            Call("real", beaconJoint, beaconPassEvent), Sp, Leq, Sp,
            powerBound, Sp, Plus, Sp,
            Call("totalVariation", inducedMass, idealMass));
        Formula sufficiency = Seq(
            Open,
            D(0), Sp, Leq, Sp, epsilon, Sp, Rightarrow, RowBreak, Grp(),
            epsilon, Sp, Leq, Sp, D(1), Sp, Rightarrow, RowBreak, Grp(),
            epsilon, Sp, Lt, Sp, implementationLoss, Sp, Rightarrow,
            RowBreak, Grp(), sufficiencyConclusion,
            Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            seed, Comma, Sp, coin, Comma, Sp, input, Comma, Sp, output, Comma, Sp,
            certificateType, Comma, Sp, anchor, Comma, Sp, task, Colon, Sp, type,
            Comma, RowBreak, Grp(),
            Typeclass("Finite", seed), Comma, Sp,
            Typeclass("MeasurableSpace", seed), Comma, Sp,
            Typeclass("MeasurableSingletonClass", seed), Comma, RowBreak, Grp(),
            Typeclass("Finite", coin), Comma, Sp,
            Typeclass("MeasurableSpace", coin), Comma, Sp,
            Typeclass("MeasurableSingletonClass", coin), Comma, RowBreak, Grp(),
            Typeclass("Fintype", input), Comma, Sp,
            Typeclass("MeasurableSpace", input), Comma, Sp,
            Typeclass("MeasurableSingletonClass", input), Comma, RowBreak, Grp(),
            Typeclass("Finite", anchor), Comma, Sp,
            Typeclass("MeasurableSpace", anchor), Comma, Sp,
            Typeclass("MeasurableSingletonClass", anchor), Comma, RowBreak, Grp(),
            Typeclass("Finite", task), Comma, Sp,
            Typeclass("MeasurableSpace", task), Comma, Sp,
            Typeclass("MeasurableSingletonClass", task), Comma, RowBreak, Grp(),
            deployment, Colon, Sp, Call("PMF", input), Comma, Sp,
            expected, Colon, Sp, behaviorType, Comma, RowBreak, Grp(),
            budget, Colon, Sp, naturals, Comma, Sp,
            epsilon, Comma, Sp, delta, Colon, Sp, reals, Comma, RowBreak, Grp(),
            seedLaw, Colon, Sp, Call("PMF", seed), Comma, Sp,
            coinLaw, Colon, Sp, Call("PMF", coin), Comma, RowBreak, Grp(),
            partySuite, Colon, Sp, Arrow(seed, suiteType), Comma, Sp,
            certificate, Colon, Sp, Arrow(seed, certificateType), Comma,
            RowBreak, Grp(),
            verifier, Colon, Sp, verifierType, Comma, Sp,
            coSelected, Colon, Sp, strategyType, Comma, RowBreak, Grp(),
            taskLaw, Colon, Sp, Call("PMF", task), Comma, Sp,
            anchorLaw, Colon, Sp, Call("PMF", anchor), Comma, RowBreak, Grp(),
            suiteMap, Colon, Sp, Arrow(anchor, suiteType), Comma, Sp,
            implementation, Colon, Sp, behaviorType, Comma, RowBreak, Grp(),
            Operatorname, Grp(F.Id("let")), Open,
            lossDefinition, Comma, RowBreak, Grp(),
            partyJointDefinition, Comma, RowBreak, Grp(),
            beaconJointDefinition, Comma, RowBreak, Grp(),
            partyRecordDefinition, Comma, RowBreak, Grp(),
            honestRecordDefinition, Comma, RowBreak, Grp(),
            inducedLawDefinition, Comma, RowBreak, Grp(),
            idealLawDefinition, Close, Semi, RowBreak, Grp(),
            necessity, Sp, Land, Sp, RowBreak, Grp(),
            sufficiency, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
