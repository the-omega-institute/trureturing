using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Decision;

internal sealed class SafeActionRefinementMonotonicityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Decision/SafeActionRefinementMonotonicity."
            + "safe_action_refinement_monotonicity";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finer readout enlarges the action set safe throughout the current fiber.",
        H("Safe Actions Under Readout Refinement"),
        Blocks(Describe.Lean(
            DescribeId.Create("safe-action-refinement-monotonicity"),
            DeclarationHandle.Create(Declaration),
            H("Refinement enlarges the fiber-safe action set"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The state-wise legality predicate is a source primitive. For a readout and "
                        + "current state, the displayed action set contains exactly those actions "
                        + "legal at every state in the same readout fiber.")),
                Paragraph(Text(
                    "The factorization q = f composed with r makes the current r-fiber a subset "
                        + "of the current q-fiber. Intersecting the same legal-action family over "
                        + "the smaller fiber can only enlarge the result.")),
                Paragraph(Text(
                    "The Lean proof applies Mathlib's bounded-intersection antitonicity theorem "
                        + "to the fiber inclusion."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula SafeActions(
        Formula stateType,
        Formula actionType,
        Formula readout,
        Formula legal,
        Formula current)
    {
        Formula state = F.Id("y");
        Formula action = F.Id("a");
        Formula sameFiber = new Formula.Relation(
            Apply(readout, state),
            FormulaRelationOperator.Equal,
            Apply(readout, current));
        Formula legalAtState = Apply(Apply(legal, state), action);
        Formula safeAtEveryFiberState = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("y"),
            stateType,
            new Formula.Logic(
                sameFiber,
                FormulaLogicOperator.Implies,
                legalAtState));

        return new Formula.SetBuilder(safeAtEveryFiberState, action, actionType);
    }

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula proposition = F.Id("Prop");
        Formula stateType = F.Id("X");
        Formula coarseType = F.Id("Q");
        Formula fineType = F.Id("R");
        Formula actionType = F.Id("A");
        Formula coarse = F.Id("q");
        Formula fine = F.Id("r");
        Formula legal = F.Id("Legal");
        Formula factor = F.Id("f");
        Formula current = F.Id("x");
        Formula factorization = new Formula.Relation(
            coarse,
            FormulaRelationOperator.Equal,
            Seq(factor, Sp, Circ, Sp, fine));
        Formula inclusion = Seq(
            SafeActions(stateType, actionType, coarse, legal, current),
            Sp,
            Subseteq,
            Sp,
            SafeActions(stateType, actionType, fine, legal, current));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("X"), type),
                new Formula.BoundVariable(FormulaIdentifier.Create("Q"), type),
                new Formula.BoundVariable(FormulaIdentifier.Create("R"), type),
                new Formula.BoundVariable(FormulaIdentifier.Create("A"), type),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("q"),
                    Arrow(stateType, coarseType)),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("r"),
                    Arrow(stateType, fineType)),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("Legal"),
                    Arrow(stateType, Arrow(actionType, proposition))),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("f"),
                    Arrow(fineType, coarseType)),
                new Formula.BoundVariable(FormulaIdentifier.Create("x"), stateType),
            ],
            new Formula.Logic(
                factorization,
                FormulaLogicOperator.Implies,
                inclusion)));
    }
}
