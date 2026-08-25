using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Termination;

internal sealed class StoppingContinuationReopeningDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed stages can close while persistent parameter changes repeatedly create new defects.",
        H("Stopping, Continuation, and Reopening"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("stopping-continuation-reopening"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Termination/StoppingContinuationReopening."
                        + "stopping_continuation_reopening"),
                H("Stagewise completion coexists with infinite genuine reopening"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The stopping conjuncts give exact source definitions. Target closure "
                            + "uses the canonical `defectRelation`; approximate closure uses the "
                            + "supremum of metric target diameters over readout fibers. Empty fibers "
                            + "contribute zero and unbounded diameters contribute top. Budget "
                            + "stopping requires a feasible action and takes an extended nonnegative "
                            + "supremum: positive gain at zero cost and unbounded ratios contribute "
                            + "top. Method stopping is the literal value equation.")),
                    Paragraph(Text(
                        "Local completion checks the supplied domain, target, and precision; the "
                            + "source gives no operation-family action on that closure predicate. "
                            + "The source does not state whether persistent parameter change occurs "
                            + "at every adjacent stage or merely infinitely often. The theorem uses "
                            + "their weakest common reading: one fixed field changes frequently. "
                            + "A reopening requires one of the five allowed changes and a canonical "
                            + "defect pair above the next precision that was absent above the current "
                            + "precision.")),
                    Paragraph(Text(
                        "The source supplies no mechanism by which a definition-language change "
                            + "alters the readout or residual family. The change remains an allowed "
                            + "trigger, but this document does not invent a language action.")),
                    Paragraph(Text(
                        "The final conjunct exhibits natural-number stages with nonempty object "
                            + "domains and real-valued targets. Each fixed stage is "
                            + "closed, while every transition changes the target and creates a "
                            + "nonempty defect. Hence reopening occurs frequently at `atTop`.")),
                    Paragraph(Text(
                        "No finiteness, decidable equality, measurability, nonempty-domain premise, "
                            + "monotonicity, or extra order law is added. The target metric is exactly "
                            + "the structure requested by approximate closure."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula At(Formula sequence, Formula stage) =>
        Apply(sequence, stage);

    private static Formula Next(Formula stage) =>
        Add(stage, Num(1));

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Or, right);

    private static Formula IffFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Nonempty(Formula value) =>
        Call("Nonempty", value);

    private static Formula Defect(Formula readout, Formula target) =>
        Call("defectRelation", readout, target);

    private static Formula Restrict(Formula concept, Formula domain) =>
        Call("restrict", concept, domain);

    private static Formula DomainDefect(
        Formula readout,
        Formula target,
        Formula precision,
        Formula domain) =>
        Call(
            "inter",
            Call(
                "inter",
                Defect(readout, target),
                Call("distanceAbove", target, precision)),
            Call("square", domain));

    private static Formula SetDifference(Formula left, Formula right) =>
        Seq(Open, left, Close, Sp, Setminus, Sp, Open, right, Close);

    private static Formula Ratio(Formula gain, Formula cost, Formula decision) =>
        new Formula.Fraction(Apply(gain, decision), Apply(cost, decision));

    private static Formula SetSuchThat(Formula value, Formula condition) =>
        Seq(OpenBrace, value, Sp, Mid, Sp, condition, CloseBrace);

    private static Formula Conjunct(Formula clause) =>
        Seq(Open, clause, Close, Sp, Land);

    private static Formula EveryStage(Formula stage, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"),
            F.Id("Nat"),
            body);

    private static Formula ParameterAt(Formula parameters, Formula stage, string field) =>
        Call(field, At(parameters, stage));

    private static Formula TheoremFormula()
    {
        Formula q = F.Id("q");
        Formula target = F.Id("T");
        Formula epsilon = Varepsilon;
        Formula decision = F.Id("d");
        Formula cost = F.Id("c");
        Formula gain = F.Id("Gain");
        Formula budget = F.Id("L");
        Formula threshold = LambdaLower;
        Formula method = F.Id("M");
        Formula system = F.Id("S");
        Formula evidence = F.Id("E");
        Formula noProposal = F.Id("NoProposal");
        Formula parameters = F.Id("P");
        Formula current = F.Id("P0");
        Formula next = F.Id("P1");
        Formula currentLanguage = F.Id("D0");
        Formula nextLanguage = F.Id("D1");
        Formula stage = F.Id("n");
        Formula languages = F.Id("D");
        Formula systems = F.Id("Q");

        Formula clause1 = IffFormula(
            Call("Closed", q, target),
            Equal(Defect(q, target), Emptyset));

        Formula clause2 = IffFormula(
            Call("ApproximatelyClosed", q, target, epsilon),
            LessOrEqual(Call("worstFiberDefect", q, target), epsilon));

        Formula feasibleDecision = LessOrEqual(Apply(cost, decision), budget);
        Formula budgetStop = Call("BudgetStop", cost, gain, budget, threshold);
        Formula ratioSet = SetSuchThat(Ratio(gain, cost, decision), feasibleDecision);
        Formula clause3 = IffFormula(
            budgetStop,
            And(
                Nonempty(SetSuchThat(decision, feasibleDecision)),
                LessOrEqual(Call("iSup", ratioSet), threshold)));

        Formula clause5 = IffFormula(
            Call("MethodStopped", method, system, evidence, noProposal),
            Equal(Apply(method, system, evidence), noProposal));

        Formula clause6 = IffFormula(
            Call("LocallyComplete", parameters, q),
            Call(
                "ApproximatelyClosed",
                Restrict(q, Call("objectDomain", parameters)),
                Restrict(Call("target", parameters), Call("objectDomain", parameters)),
                Call("precision", parameters)));

        Formula domainFrequentlyChanges = Call(
            "FrequentlyAtTop",
            SetSuchThat(
                stage,
                NotEqual(
                    ParameterAt(parameters, stage, "objectDomain"),
                    ParameterAt(parameters, Next(stage), "objectDomain"))));
        Formula targetFrequentlyChanges = Call(
            "FrequentlyAtTop",
            SetSuchThat(
                stage,
                NotEqual(
                    ParameterAt(parameters, stage, "target"),
                    ParameterAt(parameters, Next(stage), "target"))));
        Formula precisionFrequentlyChanges = Call(
            "FrequentlyAtTop",
            SetSuchThat(
                stage,
                NotEqual(
                    ParameterAt(parameters, stage, "precision"),
                    ParameterAt(parameters, Next(stage), "precision"))));
        Formula operationsFrequentlyChange = Call(
            "FrequentlyAtTop",
            SetSuchThat(
                stage,
                NotEqual(
                    ParameterAt(parameters, stage, "operationFamily"),
                    ParameterAt(parameters, Next(stage), "operationFamily"))));
        Formula clause7 = IffFormula(
            Call("OpenWorldSequence", parameters),
            Or(
                domainFrequentlyChanges,
                Or(
                    targetFrequentlyChanges,
                    Or(precisionFrequentlyChanges, operationsFrequentlyChange))));

        Formula reopeningChange = Or(
            NotEqual(Call("objectDomain", current), Call("objectDomain", next)),
            Or(
                NotEqual(Call("target", current), Call("target", next)),
                Or(
                    NotEqual(Call("precision", current), Call("precision", next)),
                    Or(
                        NotEqual(
                            Call("operationFamily", current),
                            Call("operationFamily", next)),
                        NotEqual(currentLanguage, nextLanguage)))));
        Formula currentDomain = Call("objectDomain", current);
        Formula nextDomain = Call("objectDomain", next);
        Formula oldDefects = DomainDefect(
            q,
            Call("target", current),
            Call("precision", current),
            currentDomain);
        Formula newDefects = DomainDefect(
            q,
            Call("target", next),
            Call("precision", next),
            nextDomain);
        Formula newResidual = Nonempty(SetDifference(newDefects, oldDefects));
        Formula clause8 = IffFormula(
            Call("Reopens", current, next, currentLanguage, nextLanguage, q),
            And(reopeningChange, newResidual));

        Formula stageDomainNonempty = EveryStage(
            stage,
            Nonempty(ParameterAt(parameters, stage, "objectDomain")));
        Formula everyStageComplete = EveryStage(
            stage,
            Call("LocallyComplete", At(parameters, stage), At(systems, stage)));
        Formula frequentReopening = Call(
            "FrequentlyAtTop",
            SetSuchThat(
                stage,
                Call(
                    "Reopens",
                    At(parameters, stage),
                    At(parameters, Next(stage)),
                    At(languages, stage),
                    At(languages, Next(stage)),
                    At(systems, stage))));
        Formula witnessBody = And(
            stageDomainNonempty,
            And(
                Call("OpenWorldSequence", parameters),
                And(
                    everyStageComplete,
                    frequentReopening)));
        Formula clause9 = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [
                new(
                    FormulaIdentifier.Create("P"),
                    new Formula.TypeArrow(
                        F.Id("Nat"),
                        Call("LocalParameters", F.Id("Nat"), F.Id("Real"),
                            F.Id("Unit")))),
                new(
                    FormulaIdentifier.Create("D"),
                    new Formula.TypeArrow(
                        F.Id("Nat"),
                        Call("Set", F.Id("Unit")))),
                new(
                    FormulaIdentifier.Create("Q"),
                    new Formula.TypeArrow(
                        F.Id("Nat"),
                        Call("Concept", F.Id("Nat"), F.Id("Real")))),
            ],
            witnessBody);

        return Disp(new Formula.Aligned([
            Conjunct(clause1),
            Conjunct(clause2),
            Conjunct(clause3),
            Conjunct(clause5),
            Conjunct(clause6),
            Conjunct(clause7),
            Conjunct(clause8),
            clause9,
        ]));
    }
}
