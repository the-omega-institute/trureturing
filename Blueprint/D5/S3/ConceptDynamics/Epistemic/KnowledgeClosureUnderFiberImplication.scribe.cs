using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Epistemic;

internal sealed class KnowledgeClosureUnderFiberImplicationDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Epistemic/KnowledgeClosureUnderFiberImplication.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Knowledge is preserved by implications valid on the admissible evidence fiber; "
            + "structural knowledge supplies robust knowledge, and a Boolean model separates "
            + "fiber validity from global implication.",
        H("Knowledge Closure under Fiber Implication"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("knowledge-closure-under-fiber-implication"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "knowledge_closure_under_fiber_implication"),
                H("Knowledge is closed under fiber-valid implication"),
                StatementSource.FromAuthor(ClosureFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A fiber implication needs to carry P to Q only at admissible states "
                            + "whose evidence agrees with the anchor; it makes no claim about "
                            + "states outside that fiber.")),
                    Paragraph(Text(
                        "Robust knowledge supplies P at the admissible anchor and throughout "
                            + "its admissible evidence fiber. Applying the fiber implication "
                            + "at the anchor and at each such state establishes robust "
                            + "knowledge of Q."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("structural-knowledge-implies-robust-knowledge"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "structural_knowledge_implies_robust_knowledge"),
                H("Structural knowledge implies robust knowledge"),
                StatementSource.FromAuthor(StructuralFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Structural knowledge makes the predicate constant on every evidence "
                        + "fiber and records its truth at an admissible anchor. For any "
                        + "admissible state with the anchor's evidence, fiber constancy "
                        + "transfers the anchor truth to that state, which is precisely the "
                        + "remaining robust-knowledge condition."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("fiber-implication-is-not-global-implication"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "fiber_implication_not_global_counterexample"),
                H("Fiber implication need not hold globally"),
                StatementSource.FromAuthor(CounterexampleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Take Boolean states with only true admissible, constant Unit evidence, "
                        + "P always true, and Q true exactly at the state true. The fiber "
                        + "implication is valid because its admissible fiber contains no "
                        + "counterexample, and both P and Q are robustly known at true. The "
                        + "ambient implication nevertheless fails at false, proving that "
                        + "fiber validity is strictly weaker than global validity."))),
                DescribeRole.Lemma))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula ImpliesFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula LambdaFormula(Formula variable, Formula body) =>
        Seq(Lambda, Sp, variable, Comma, Sp, body);

    private static Formula Robust(
        Formula admissible,
        Formula evidence,
        Formula predicate,
        Formula anchor) =>
        Call("robustKnowledge", admissible, evidence, predicate, anchor);

    private static Formula FiberImplication(
        Formula admissible,
        Formula evidence,
        Formula premise,
        Formula conclusion,
        Formula anchor) =>
        Call("fiberImplication", admissible, evidence, premise, conclusion, anchor);

    private static Formula Structural(
        Formula admissible,
        Formula evidence,
        Formula predicate,
        Formula anchor) =>
        Call("structuralKnowledge", admissible, evidence, predicate, anchor);

    private static Formula ClosureFormula()
    {
        Formula stateType = F.Id("X");
        Formula evidenceType = F.Id("B");
        Formula proposition = F.Id("Prop");
        Formula admissible = F.Id("A");
        Formula evidence = F.Id("e");
        Formula premise = F.Id("P");
        Formula conclusion = F.Id("Q");
        Formula anchor = F.Id("a");
        Formula hypotheses = And(
            Robust(admissible, evidence, premise, anchor),
            FiberImplication(admissible, evidence, premise, conclusion, anchor));
        Formula result = Robust(admissible, evidence, conclusion, anchor);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [.. ContextVariables(
                stateType,
                evidenceType,
                proposition,
                admissible,
                evidence,
                premise,
                conclusion,
                anchor)],
            ImpliesFormula(hypotheses, result)));
    }

    private static Formula StructuralFormula()
    {
        Formula stateType = F.Id("X");
        Formula evidenceType = F.Id("B");
        Formula proposition = F.Id("Prop");
        Formula admissible = F.Id("A");
        Formula evidence = F.Id("e");
        Formula predicate = F.Id("P");
        Formula anchor = F.Id("a");

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [.. ContextVariables(
                stateType,
                evidenceType,
                proposition,
                admissible,
                evidence,
                predicate,
                null,
                anchor)],
            ImpliesFormula(
                Structural(admissible, evidence, predicate, anchor),
                Robust(admissible, evidence, predicate, anchor))));
    }

    private static Formula CounterexampleFormula()
    {
        Formula state = F.Id("x");
        Formula truth = F.Id("true");
        Formula admissible = LambdaFormula(state, Equal(state, truth));
        Formula evidence = LambdaFormula(state, F.Id("unit"));
        Formula premise = LambdaFormula(state, F.Id("True"));
        Formula conclusion = LambdaFormula(state, Equal(state, truth));
        Formula globalImplication = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("x"),
            F.Id("Bool"),
            ImpliesFormula(F.Id("True"), Equal(state, truth)));
        Formula body = And(
            Robust(admissible, evidence, premise, truth),
            And(
                FiberImplication(admissible, evidence, premise, conclusion, truth),
                And(
                    new Formula.Not(globalImplication),
                    Robust(admissible, evidence, conclusion, truth))));

        return Disp(Seq(
            F.Id("X"), Sp, Eq, Sp, F.Id("Bool"), Comma, Sp,
            F.Id("B"), Sp, Eq, Sp, F.Id("Unit"), Comma, RowBreak, Grp(),
            body, Dot));
    }

    private static Formula.BoundVariable[] ContextVariables(
        Formula stateType,
        Formula evidenceType,
        Formula proposition,
        Formula admissible,
        Formula evidence,
        Formula premise,
        Formula? conclusion,
        Formula anchor)
    {
        List<Formula.BoundVariable> variables =
        [
            Bound("X", F.Id("Type")),
            Bound("B", F.Id("Type")),
            Bound("A", Arrow(stateType, proposition)),
            Bound("e", Arrow(stateType, evidenceType)),
            Bound("P", Arrow(stateType, proposition)),
        ];

        if (conclusion is not null)
        {
            variables.Add(Bound("Q", Arrow(stateType, proposition)));
        }

        variables.Add(Bound("a", stateType));
        return [.. variables];
    }
}
