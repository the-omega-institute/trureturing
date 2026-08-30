using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscapeSignatures;

internal sealed class AdjudicationSignatureNecessityDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/DefinitionEscapeSignatures/"
            + "AdjudicationSignatureNecessity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every coordinate of the sufficient adjudication signature has a finite "
            + "deletion witness among the post-OP1 surviving consumers.",
        H("Coordinate Necessity of the Adjudication Signature"),
        Blocks(
            DirectionDefinition(
                "freeze-visibility-direction-definition",
                "FreezeVisibilityDirection",
                "Freeze-visibility deletion witness",
                FreezeDirectionFormula(),
                "NonAnticipating is true when evidence first appears at decision and "
                    + "false when the same evidence is already visible at freeze."),
            DirectionDefinition(
                "decision-visibility-direction-definition",
                "DecisionVisibilityDirection",
                "Decision-visibility deletion witness",
                DecisionDirectionFormula(),
                "NonAnticipating is true when the selected evidence is decision-visible "
                    + "and false when it remains invisible."),
            DirectionDefinition(
                "direct-contamination-direction-definition",
                "DirectContaminationDirection",
                "Direct-contamination deletion witness",
                ContaminationDirectionFormula(),
                "NonAnticipating is true with empty direct dependencies and false after "
                    + "adding only the selected evidence to evidenceDependencies."),
            DirectionDefinition(
                "role-projection-direction-definition",
                "RoleProjectionDirection",
                "Role-projection deletion witness",
                RoleDirectionFormula(),
                "AdmissibleJudge is true with one valid in-prefix adjudicate event and "
                    + "false with the empty ledger; the snapshot is identical."),
            Describe.Lean(
                DescribeId.Create("adjudication-signature-coordinate-necessity"),
                DeclarationHandle.Create(
                    Prefix + "adjudication_signature_coordinate_necessity"),
                H("All four surviving coordinate directions are necessary"),
                StatementSource.FromAuthor(AggregateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The first three directions select NonAnticipating, whose OP1 "
                            + "factorization theorem is frozen in the imported sufficiency "
                            + "module. The fourth selects AdmissibleJudge, whose OP1 "
                            + "factorization theorem is frozen there as well.")),
                    Paragraph(Text(
                        "Each closed direction fixes the same nonempty Boolean record set and "
                            + "evidence point, states SameOut, equates all three unablated "
                            + "signature fields, separates the selected field, and reverses "
                            + "the consumer truth value.")),
                    Paragraph(Text(
                        "Target laundering is not selected: its OP1 antecedent is false by the "
                            + "frozen target_laundering_signature_counterexample. A meaningful "
                            + "target-laundering necessity question must first enrich and "
                            + "re-establish a sufficient signature."))),
                DescribeRole.Theorem))));

    private static DocumentBlock.Describe DirectionDefinition(
        string id,
        string declaration,
        string heading,
        Formula formula,
        string commentary) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(heading),
            StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(commentary))),
            DescribeRole.Definition);

    private static Formula AggregateFormula() => Disp(And(
        Call("FreezeVisibilityDirection"),
        And(
            Call("DecisionVisibilityDirection"),
            And(
                Call("DirectContaminationDirection"),
                Call("RoleProjectionDirection")))));

    private static Formula FreezeDirectionFormula()
    {
        Formula positive = F.Id("positive"), negative = F.Id("negative");
        Formula clean = F.Id("clean"), exposed = F.Id("freezeExposed");
        return DirectionFormula(
            Signature(F.Id("emptyLedger"), clean, Valid(clean)),
            Signature(F.Id("emptyLedger"), exposed, Valid(exposed)),
            Call("SameOutNA", F.Id("records"), F.Id("true")),
            positive,
            negative,
            ["decisionVisible", "directlyContaminated", "roleProjection"],
            "freezeVisible",
            Call("NonAnticipating", clean, F.Id("true")),
            Call("NonAnticipating", exposed, F.Id("true")));
    }

    private static Formula DecisionDirectionFormula()
    {
        Formula positive = F.Id("positive"), negative = F.Id("negative");
        Formula clean = F.Id("clean"), hidden = F.Id("decisionHidden");
        return DirectionFormula(
            Signature(F.Id("emptyLedger"), clean, Valid(clean)),
            Signature(F.Id("emptyLedger"), hidden, Valid(hidden)),
            Call("SameOutNA", F.Id("records"), F.Id("true")),
            positive,
            negative,
            ["freezeVisible", "directlyContaminated", "roleProjection"],
            "decisionVisible",
            Call("NonAnticipating", clean, F.Id("true")),
            Call("NonAnticipating", hidden, F.Id("true")));
    }

    private static Formula ContaminationDirectionFormula()
    {
        Formula positive = F.Id("positive"), negative = F.Id("negative");
        Formula clean = F.Id("clean"), contaminated = F.Id("contaminated");
        return DirectionFormula(
            Signature(F.Id("emptyLedger"), clean, Valid(clean)),
            Signature(F.Id("emptyLedger"), contaminated, Valid(contaminated)),
            Call("SameOutNA", F.Id("records"), F.Id("true")),
            positive,
            negative,
            ["freezeVisible", "decisionVisible", "roleProjection"],
            "directlyContaminated",
            Call("NonAnticipating", clean, F.Id("true")),
            Call("NonAnticipating", contaminated, F.Id("true")));
    }

    private static Formula RoleDirectionFormula()
    {
        Formula positive = F.Id("positive"), negative = F.Id("negative");
        Formula clean = F.Id("clean");
        Formula emptyValid = Valid(clean);
        return DirectionFormula(
            Signature(F.Id("judgeLedger"), clean, Call("judgeValid")),
            Signature(F.Id("emptyLedger"), clean, emptyValid),
            Call("SameOutAJ", F.Id("records"), F.Id("true")),
            positive,
            negative,
            ["freezeVisible", "decisionVisible", "directlyContaminated"],
            "roleProjection",
            Call(
                "AdmissibleJudge",
                F.Id("judgeLedger"),
                clean,
                Call("judgeValid"),
                F.Id("true")),
            Call(
                "AdmissibleJudge",
                F.Id("emptyLedger"),
                clean,
                emptyValid,
                F.Id("true")));
    }

    private static Formula DirectionFormula(
        Formula positiveValue,
        Formula negativeValue,
        Formula sameOut,
        Formula positive,
        Formula negative,
        string[] equalFields,
        string unequalField,
        Formula positiveConsumer,
        Formula negativeConsumer)
    {
        Formula body = And(
            sameOut,
            And(
                Equal(Field(equalFields[0], positive), Field(equalFields[0], negative)),
                And(
                    Equal(Field(equalFields[1], positive), Field(equalFields[1], negative)),
                    And(
                        Equal(
                            Field(equalFields[2], positive),
                            Field(equalFields[2], negative)),
                        And(
                            NotEqual(
                                Field(unequalField, positive),
                                Field(unequalField, negative)),
                            IffFormula(
                                positiveConsumer,
                                new Formula.Not(negativeConsumer)))))));

        return Disp(Seq(
            Let("positive", positiveValue),
            Let("negative", negativeValue),
            body));
    }

    private static Formula Signature(
        Formula ledger,
        Formula snapshot,
        Formula valid) =>
        Call("adjudicationSignature", F.Id("records"), ledger, snapshot, valid);

    private static Formula Valid(Formula snapshot) =>
        Call("emptyValid", snapshot);

    private static Formula Field(string field, Formula value) =>
        Call(field, value);

    private static Formula Let(string name, Formula value) =>
        Seq(
            Operatorname,
            Grp(F.Id("let")),
            Sp,
            F.Id(name),
            Sp,
            Eq,
            Sp,
            value,
            Comma,
            Sp);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula IffFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
