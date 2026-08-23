using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InstitutionalCapture;

internal sealed class ProceduralJusticeNotOutcomeCorrectDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/InstitutionalCapture/ProceduralJusticeNotOutcomeCorrect.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A judgment can use all public facts and rules yet be wrong when their joint readout "
            + "does not determine truth.",
        H("Procedural Justice Does Not Guarantee a Correct Outcome"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("every-procedurally-complete-judgment-is-incorrect"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "every_procedurally_complete_judgment_is_incorrect"),
                H("A defective public join makes every procedural judgment incorrect"),
                StatementSource.FromAuthor(EveryProceduralJudgmentIsIncorrectFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "On an inhabited case space, a nonempty defect in the joint facts-and-rules "
                            + "readout gives two publicly indistinguishable cases with different "
                            + "truth values.")),
                    Paragraph(Text(
                        "Every procedurally complete judgment factors through that joint readout, "
                            + "so it cannot distinguish the defective pair. If it agreed with truth "
                            + "on every case, truth would factor through the same readout, contrary "
                            + "to the defect. Thus each such judgment is wrong somewhere."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("sufficient-joint-readout-permits-correct-outcome"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "sufficient_joint_readout_permits_correct_outcome"),
                H("A sufficient public join permits a correct procedural judgment"),
                StatementSource.FromAuthor(SufficientJointReadoutFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When factual truth factors through the joint facts-and-rules readout, truth "
                        + "itself can serve as the judgment. The factorization makes that judgment "
                        + "procedurally complete, while choosing truth makes it outcome-correct."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("procedural-completeness-permits-wrong-outcome"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "procedural_completeness_permits_wrong_outcome"),
                H("Procedural completeness can coexist with unavoidable error"),
                StatementSource.FromAuthor(ProceduralCompletenessPermitsWrongOutcomeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take Boolean cases, let both public readouts be constant, let truth be the "
                            + "identity, and let the exhibited judgment always return false. The "
                            + "judgment is a function of the public join but disagrees with truth "
                            + "at the true case.")),
                    Paragraph(Text(
                        "The false and true cases have the same public facts and rules but opposite "
                            + "truth values, so they form a defect of the joint readout. The general "
                            + "obstruction then shows more than one mistaken judgment: every "
                            + "procedurally complete Boolean judgment must fail on some case."))),
                DescribeRole.Theorem))));

    private static Formula Concept(Formula stateType, Formula valueType) =>
        Call("Concept", stateType, valueType);

    private static Formula JointReadout(Formula facts, Formula rules) =>
        Call("conceptJoin", facts, rules);

    private static Formula ProcedurallyComplete(
        Formula facts,
        Formula rules,
        Formula judgment) =>
        Call("ProcedurallyComplete", facts, rules, judgment);

    private static Formula OutcomeCorrect(Formula truth, Formula judgment) =>
        Call("OutcomeCorrect", truth, judgment);

    private static Formula DefectNonempty(
        Formula facts,
        Formula rules,
        Formula truth) =>
        Call("Nonempty", Call("defectRelation", JointReadout(facts, rules), truth));

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula ImpliesFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula MismatchExists(
        Formula stateType,
        Formula judgment,
        Formula truth)
    {
        Formula caseValue = F.Id("case");

        return new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("case"),
            stateType,
            NotEqual(Apply(judgment, caseValue), Apply(truth, caseValue)));
    }

    private static Formula EveryProceduralJudgmentIsIncorrectFormula()
    {
        Formula type = F.Id("Type");
        Formula caseType = F.Id("Case");
        Formula factType = F.Id("Fact");
        Formula ruleType = F.Id("Rule");
        Formula verdictType = F.Id("Verdict");
        Formula facts = F.Id("facts");
        Formula rules = F.Id("rules");
        Formula truth = F.Id("truth");
        Formula judgment = F.Id("judgment");
        Formula judgmentType = Concept(caseType, verdictType);
        Formula everyJudgment = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("judgment"),
            judgmentType,
            ImpliesFormula(
                ProcedurallyComplete(facts, rules, judgment),
                MismatchExists(caseType, judgment, truth)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new(FormulaIdentifier.Create("Case"), type),
                new(FormulaIdentifier.Create("Fact"), type),
                new(FormulaIdentifier.Create("Rule"), type),
                new(FormulaIdentifier.Create("Verdict"), type),
                new(FormulaIdentifier.Create("anchor"), caseType),
                new(FormulaIdentifier.Create("facts"), Concept(caseType, factType)),
                new(FormulaIdentifier.Create("rules"), Concept(caseType, ruleType)),
                new(FormulaIdentifier.Create("truth"), judgmentType),
            ],
            ImpliesFormula(DefectNonempty(facts, rules, truth), everyJudgment)));
    }

    private static Formula SufficientJointReadoutFormula()
    {
        Formula type = F.Id("Type");
        Formula caseType = F.Id("Case");
        Formula factType = F.Id("Fact");
        Formula ruleType = F.Id("Rule");
        Formula verdictType = F.Id("Verdict");
        Formula facts = F.Id("facts");
        Formula rules = F.Id("rules");
        Formula truth = F.Id("truth");
        Formula judgment = F.Id("judgment");
        Formula judgmentType = Concept(caseType, verdictType);
        Formula correctJudgment = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("judgment"),
            judgmentType,
            And(
                ProcedurallyComplete(facts, rules, judgment),
                OutcomeCorrect(truth, judgment)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new(FormulaIdentifier.Create("Case"), type),
                new(FormulaIdentifier.Create("Fact"), type),
                new(FormulaIdentifier.Create("Rule"), type),
                new(FormulaIdentifier.Create("Verdict"), type),
                new(FormulaIdentifier.Create("facts"), Concept(caseType, factType)),
                new(FormulaIdentifier.Create("rules"), Concept(caseType, ruleType)),
                new(FormulaIdentifier.Create("truth"), judgmentType),
            ],
            ImpliesFormula(
                Call("Refines", truth, JointReadout(facts, rules)),
                correctJudgment)));
    }

    private static Formula ProceduralCompletenessPermitsWrongOutcomeFormula()
    {
        Formula boolean = F.Id("Bool");
        Formula unit = F.Id("PUnit");
        Formula facts = F.Id("facts");
        Formula rules = F.Id("rules");
        Formula truth = F.Id("truth");
        Formula judgment = F.Id("judgment");
        Formula candidate = F.Id("candidate");
        Formula publicReadoutType = Concept(boolean, unit);
        Formula judgmentType = Concept(boolean, boolean);
        Formula everyCandidate = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("candidate"),
            judgmentType,
            ImpliesFormula(
                ProcedurallyComplete(facts, rules, candidate),
                MismatchExists(boolean, candidate, truth)));
        Formula conditions = And(
            DefectNonempty(facts, rules, truth),
            And(
                ProcedurallyComplete(facts, rules, judgment),
                And(MismatchExists(boolean, judgment, truth), everyCandidate)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.Exists,
            [
                new(FormulaIdentifier.Create("facts"), publicReadoutType),
                new(FormulaIdentifier.Create("rules"), publicReadoutType),
                new(FormulaIdentifier.Create("truth"), judgmentType),
                new(FormulaIdentifier.Create("judgment"), judgmentType),
            ],
            conditions));
    }
}
