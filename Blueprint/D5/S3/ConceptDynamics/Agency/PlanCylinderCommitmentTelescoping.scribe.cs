using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Agency;

internal sealed class PlanCylinderCommitmentTelescopingDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Action-selected finite plan cylinders telescope their commitment depths.",
        H("Plan-Cylinder Commitment Telescoping"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("plan-cylinder-commitment-depth-telescopes"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Agency/PlanCylinderCommitmentTelescoping."
                        + "plan_cylinder_commitment_depth_telescopes"),
                H("Plan-cylinder commitment depth telescopes"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Each history carries a finite nonempty set of compatible complete "
                            + "future plans. A plan cylinder retains exactly those plans whose "
                            + "current prescription equals the action actually selected.")),
                    Paragraph(Text(
                        "When every next history has exactly the selected cylinder as its "
                            + "compatible-plan set, the stepwise base-two log-cardinality "
                            + "losses cancel to the initial-minus-terminal loss."))),
                DescribeRole.Theorem))));

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Typeclass(Formula proposition) =>
        Seq(OpenBracket, proposition, CloseBracket);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula TheoremFormula()
    {
        Formula historyType = F.Id("History");
        Formula planType = F.Id("Plan");
        Formula actionType = F.Id("Action");
        Formula naturals = F.Id("Nat");
        Formula compatible = F.Id("Omega");
        Formula prescription = F.Id("prescribes");
        Formula history = F.Id("history");
        Formula action = F.Id("action");
        Formula horizon = F.Id("n");
        Formula time = F.Id("t");
        Formula plan = F.Id("omega");

        Formula At(Formula function, params Formula[] arguments) =>
            Apply(function, arguments);
        Formula HistoryAt(Formula index) => At(history, index);
        Formula PlansAt(Formula index) => At(compatible, HistoryAt(index));
        Formula PrescribedAt(Formula index) =>
            At(prescription, HistoryAt(index), plan);
        Formula CylinderAt(Formula index) => Seq(
            OpenBrace,
            plan, Sp, InMacro, Sp, PlansAt(index), Sp, Mid, Sp,
            PrescribedAt(index), Sp, Eq, Sp, At(action, index),
            CloseBrace);
        Formula LogCard(Formula plans) =>
            Call("log2", Call("card", plans));
        Formula DepthAt(Formula index) => Seq(
            LogCard(PlansAt(index)), Sp, Minus, Sp, LogCard(CylinderAt(index)));

        Formula nonemptyPlans = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("h"),
            historyType,
            Seq(At(compatible, F.Id("h")), Sp, Neq, Sp, Emptyset));
        Formula cylinderStep = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("t"),
            naturals,
            Implies(
                new Formula.Relation(time, FormulaRelationOperator.LessThan, horizon),
                Equal(
                    PlansAt(Seq(time, Sp, Plus, Sp, D(1))),
                    CylinderAt(time))));
        Formula depthSum = Seq(
            Sum, Underscore,
            Grp(Seq(time, Sp, InMacro, Sp, Call("range", horizon))),
            Sp, Grp(DepthAt(time)));
        Formula endpointLoss = Seq(
            LogCard(PlansAt(D(0))), Sp, Minus, Sp, LogCard(PlansAt(horizon)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("History", TypeUniverse()),
                Bound("Plan", TypeUniverse()),
                Bound("Action", TypeUniverse()),
                Bound("Omega", Arrow(historyType, Call("Finset", planType))),
                Bound("prescribes", Arrow(historyType, Arrow(planType, actionType))),
                Bound("history", Arrow(naturals, historyType)),
                Bound("action", Arrow(naturals, actionType)),
                Bound("n", naturals),
            ],
            Implies(
                And(
                    Typeclass(Call("DecidableEq", actionType)),
                    And(nonemptyPlans, cylinderStep)),
                Equal(depthSum, endpointLoss))));
    }
}
