using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Governance;

internal sealed class InformationRefinementGovernanceDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Governance/InformationRefinementGovernance."
            + "information_refinement_expands_answers_policies_and_leakage";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Information refinement expands answerability, policy capability, and sensitive leakage.",
        H("Information Refinement and Governance"),
        Blocks(Describe.Lean(
            DescribeId.Create("information-refinement-expands-governance-capability"),
            DeclarationHandle.Create(Declaration),
            H("Information refinement expands answers, policies, and leakage"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The premise uses the canonical factorization order: the coarse readout C "
                        + "is recoverable from the refined readout D.")),
                Paragraph(Text(
                    "The conclusion combines three existing monotonicity laws without "
                        + "reproving them. Every old answerable target and implementable policy "
                        + "remains available, and adjoining the same sensitive readout preserves "
                        + "the refinement order."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula coarseType = F.Id("A");
        Formula refinedType = F.Id("B");
        Formula targetType = F.Id("Y");
        Formula actionType = F.Id("U");
        Formula sensitiveType = F.Id("S");
        Formula coarse = F.Id("C");
        Formula refined = F.Id("D");
        Formula sensitive = F.Id("K");
        Formula universe = Seq(Operatorname, Grp(F.Id("Type")));

        Formula answerInclusion = new Formula.Relation(
            Call("AnswerableTargets", coarse, targetType),
            FormulaRelationOperator.SubsetOf,
            Call("AnswerableTargets", refined, targetType));
        Formula policyInclusion = new Formula.Relation(
            Call("policyCapability", coarse, actionType),
            FormulaRelationOperator.SubsetOf,
            Call("policyCapability", refined, actionType));
        Formula leakageRefinement = Call(
            "Refines",
            Call("conceptJoin", coarse, sensitive),
            Call("conceptJoin", refined, sensitive));
        Formula conclusion = And(answerInclusion, And(policyInclusion, leakageRefinement));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("X"), universe),
                new Formula.BoundVariable(FormulaIdentifier.Create("A"), universe),
                new Formula.BoundVariable(FormulaIdentifier.Create("B"), universe),
                new Formula.BoundVariable(FormulaIdentifier.Create("Y"), universe),
                new Formula.BoundVariable(FormulaIdentifier.Create("U"), universe),
                new Formula.BoundVariable(FormulaIdentifier.Create("S"), universe),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("C"), Arrow(state, coarseType)),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("D"), Arrow(state, refinedType)),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("K"), Arrow(state, sensitiveType)),
            ],
            new Formula.Logic(
                Call("Refines", coarse, refined),
                FormulaLogicOperator.Implies,
                conclusion)));
    }
}
