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
                        "The first five conjuncts give exact stopping definitions. Target closure "
                            + "uses the canonical `defectRelation`; approximate closure uses the "
                            + "supplied comparison; and budget stopping uses a total pointwise "
                            + "condition. For real ratios it agrees with the displayed `sSup` "
                            + "formula when the feasible set is nonempty and the ratio set is "
                            + "bounded above. Method stopping is the literal method value equation.")),
                    Paragraph(Text(
                        "Local completion fixes all four parameters `(X,T,I,epsilon)`. An open-world "
                            + "sequence changes at least one of them at every adjacent stage. A "
                            + "reopening requires both one of the five allowed changes, including "
                            + "definition language, and a nonempty canonical defect on the next "
                            + "object domain.")),
                    Paragraph(Text(
                        "The final conjunct exhibits natural-number stages with nonempty object "
                            + "domains and a nonempty Boolean target type. Each fixed stage is "
                            + "closed, while every transition changes the target and creates a "
                            + "nonempty defect. Hence reopening occurs frequently at `atTop`.")),
                    Paragraph(Text(
                        "The comparison and division symbols denote only the supplied generic "
                            + "operations. No finiteness, decidable equality, measurability, "
                            + "nonempty-domain premise, monotonicity, or order laws are added to "
                            + "the generic stopping definitions."))),
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

    private static Formula ImpliesFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula IffFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Nonempty(Formula value) =>
        Call("Nonempty", value);

    private static Formula Defect(Formula readout, Formula target) =>
        Call("defectRelation", readout, target);

    private static Formula Restrict(Formula concept, Formula domain) =>
        Call("restrict", concept, domain);

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
        Formula deviation = Delta;
        Formula epsilon = Varepsilon;
        Formula decisionType = F.Id("Decision");
        Formula decision = F.Id("d");
        Formula cost = F.Id("c");
        Formula gain = F.Id("Gain");
        Formula budget = F.Id("L");
        Formula threshold = LambdaLower;
        Formula method = F.Id("M");
        Formula system = F.Id("S");
        Formula evidence = F.Id("E");
        Formula noProposal = F.Id("NoProposal");
        Formula objectDomain = F.Id("X");
        Formula operations = F.Id("I");
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
            Call("ApproximatelyClosed", deviation, q, target, epsilon),
            LessOrEqual(Apply(deviation, q, target), epsilon));

        Formula feasibleDecision = LessOrEqual(Apply(cost, decision), budget);
        Formula pointwiseStop = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("d"),
            decisionType,
            ImpliesFormula(
                feasibleDecision,
                LessOrEqual(Ratio(gain, cost, decision), threshold)));
        Formula budgetStop = Call("BudgetStop", cost, gain, budget, threshold);
        Formula clause3 = IffFormula(budgetStop, pointwiseStop);

        Formula feasibleSet = SetSuchThat(decision, feasibleDecision);
        Formula ratioSet = SetSuchThat(Ratio(gain, cost, decision), feasibleDecision);
        Formula supremumPremises = And(
            Nonempty(feasibleSet),
            Call("BddAbove", ratioSet));
        Formula clause4 = ImpliesFormula(
            supremumPremises,
            IffFormula(
                budgetStop,
                LessOrEqual(Call("sSup", ratioSet), threshold)));

        Formula clause5 = IffFormula(
            Call("MethodStopped", method, system, evidence, noProposal),
            Equal(Apply(method, system, evidence), noProposal));

        Formula fixedParameters = Call(
            "LocalParameters",
            objectDomain,
            target,
            operations,
            epsilon);
        Formula clause6 = IffFormula(
            Call("LocallyComplete", fixedParameters, q),
            Call(
                "Closed",
                Restrict(q, objectDomain),
                Restrict(target, objectDomain)));

        Formula adjacentParameterChange = Or(
            NotEqual(
                ParameterAt(parameters, stage, "objectDomain"),
                ParameterAt(parameters, Next(stage), "objectDomain")),
            Or(
                NotEqual(
                    ParameterAt(parameters, stage, "target"),
                    ParameterAt(parameters, Next(stage), "target")),
                Or(
                    NotEqual(
                        ParameterAt(parameters, stage, "operationFamily"),
                        ParameterAt(parameters, Next(stage), "operationFamily")),
                    NotEqual(
                        ParameterAt(parameters, stage, "precision"),
                        ParameterAt(parameters, Next(stage), "precision")))));
        Formula clause7 = IffFormula(
            Call("OpenWorldSequence", parameters),
            EveryStage(stage, adjacentParameterChange));

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
        Formula nextDomain = Call("objectDomain", next);
        Formula reopeningDefect = Nonempty(Defect(
            Restrict(q, nextDomain),
            Restrict(Call("target", next), nextDomain)));
        Formula clause8 = IffFormula(
            Call("Reopens", current, next, currentLanguage, nextLanguage, q),
            And(reopeningChange, reopeningDefect));

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
            Nonempty(F.Id("Bool")),
            And(
                stageDomainNonempty,
                And(
                    Call("OpenWorldSequence", parameters),
                    And(everyStageComplete, frequentReopening))));
        Formula clause9 = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [
                new(
                    FormulaIdentifier.Create("P"),
                    new Formula.TypeArrow(
                        F.Id("Nat"),
                        Call("LocalParameters", F.Id("Nat"), F.Id("Bool"),
                            F.Id("Unit"), F.Id("Nat")))),
                new(
                    FormulaIdentifier.Create("D"),
                    new Formula.TypeArrow(
                        F.Id("Nat"),
                        Call("Set", F.Id("Unit")))),
                new(
                    FormulaIdentifier.Create("Q"),
                    new Formula.TypeArrow(
                        F.Id("Nat"),
                        Call("Concept", F.Id("Nat"), F.Id("Bool")))),
            ],
            witnessBody);

        return Disp(new Formula.Aligned([
            Conjunct(clause1),
            Conjunct(clause2),
            Conjunct(clause3),
            Conjunct(clause4),
            Conjunct(clause5),
            Conjunct(clause6),
            Conjunct(clause7),
            Conjunct(clause8),
            clause9,
        ]));
    }
}
