using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Interventions;

internal sealed class CounterfactualIdentifiabilityCriterionDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Interventions/CounterfactualIdentifiabilityCriterion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Counterfactual recovery from all single-world marginals is exactly constancy on "
            + "coupling fibers, and complete Boolean counterfactuals fail this criterion.",
        H("Counterfactual Identifiability Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("counterfactual-identifiability-is-fiber-constancy"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "counterfactual_identifiable_iff_constant_on_fiber"),
                H("Counterfactual identifiability is marginal-fiber constancy"),
                StatementSource.FromAuthor(GeneralCriterionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let a marginal map send each coupling to its complete family of "
                            + "single-world data. A target is recoverable from those data "
                            + "exactly when equal marginal families force equal target values.")),
                    Paragraph(Text(
                        "The coupling fiber over a data value is constructed as the preimage "
                            + "of that value. Thus the equality-kernel condition states "
                            + "constancy of the target on every coupling fiber."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("single-world-identifiability-is-fiber-constancy"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "boolean_counterfactual_identifiable_iff_constant_on_coupling_fibers"),
                H("Single-world identifiability is constancy on coupling fibers"),
                StatementSource.FromAuthor(BooleanCriterionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The observable record of a deterministic Boolean joint model is the "
                            + "family of outcome-count marginals indexed by intervention. A "
                            + "target Q is recoverable from that record exactly when any two "
                            + "models in the same explicitly represented coupling fiber have "
                            + "the same Q-value.")),
                    Paragraph(Text(
                        "This specializes the general factorization criterion: a target factors "
                            + "through an observable map exactly when it is constant on every "
                            + "fiber. Nonemptiness of the target type permits the factor map to "
                            + "be extended to observable records outside the map's image."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("complete-counterfactual-varies-within-a-coupling-fiber"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "boolean_counterfactual_varies_on_coupling_fiber"),
                H("The complete counterfactual varies within one coupling fiber"),
                StatementSource.FromAuthor(FiberVariationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Two deterministic Boolean joint models have the same marginal outcome "
                            + "counts under every intervention, so they occupy a single fiber of "
                            + "the all-single-world-marginals map.")),
                    Paragraph(Text(
                        "Their complete unit-level counterfactual tables nevertheless differ. "
                            + "The observable fiber therefore contains a concrete variation of "
                            + "the counterfactual target."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("complete-counterfactual-is-not-identifiable"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "boolean_counterfactual_not_identifiable"),
                H("The complete Boolean counterfactual is not identifiable"),
                StatementSource.FromAuthor(NonidentifiabilityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "If the complete unit-level counterfactual table could be recovered from "
                            + "all single-world intervention marginals, the fiber criterion would "
                            + "make it constant on every coupling fiber.")),
                    Paragraph(Text(
                        "The two-model fiber witness has identical observable marginals but "
                            + "different counterfactual tables, contradicting that required "
                            + "constancy and ruling out every such recovery map."))),
                DescribeRole.Lemma))));

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula NonemptyInstance(Formula type) =>
        Seq(
            OpenBracket,
            Operatorname,
            Grp(F.Id("Nonempty")),
            Sp,
            type,
            CloseBracket);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula ImpliesFormula(Formula hypothesis, Formula conclusion) =>
        new Formula.Logic(hypothesis, FormulaLogicOperator.Implies, conclusion);

    private static Formula IffFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Fiber(Formula data) =>
        Apply(F.Id("couplingFiber"), F.Id("allSingleWorldMarginals"), data);

    private static Formula GeneralCriterionFormula()
    {
        Formula coupling = F.Id("Coupling");
        Formula data = F.Id("Data");
        Formula value = F.Id("Value");
        Formula marginals = F.Id("marginals");
        Formula target = F.Id("Q");
        Formula factor = F.Id("f");
        Formula first = F.Id("c");
        Formula second = F.Id("cPrime");
        Formula factorization = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("f", Arrow(data, value))],
            Equal(target, Seq(factor, Sp, Circ, Sp, marginals)));
        Formula fiberConstancy = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("c", coupling), Bound("cPrime", coupling)],
            ImpliesFormula(
                Equal(Apply(marginals, first), Apply(marginals, second)),
                Equal(Apply(target, first), Apply(target, second))));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(coupling, Comma, Sp, data, Comma, Sp, value), TypeUniverse()),
            Comma, Sp, NonemptyInstance(value), Comma, RowBreak, Grp(),
            Typed(marginals, Arrow(coupling, data)), Comma, Sp,
            Typed(target, Arrow(coupling, value)), Comma, RowBreak, Grp(),
            IffFormula(factorization, fiberConstancy), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula BooleanCriterionFormula()
    {
        Formula value = F.Id("Value");
        Formula target = F.Id("Q");
        Formula coupling = F.Id("BooleanCoupling");
        Formula marginalFamily = Arrow(F.Id("Bool"), F.Id("BooleanMarginal"));
        Formula factor = F.Id("f");
        Formula observable = F.Id("allSingleWorldMarginals");
        Formula data = F.Id("mu");
        Formula firstModel = F.Id("M");
        Formula secondModel = F.Id("N");
        Formula factorType = Seq(
            Open, marginalFamily, Close, Sp, To, Sp, value);
        Formula factorization = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("f", factorType)],
            Equal(target, Seq(factor, Sp, Circ, Sp, observable)));
        Formula fiberConstancy = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("mu", marginalFamily),
                Bound("M", coupling),
                Bound("N", coupling),
            ],
            ImpliesFormula(
                And(
                    Member(firstModel, Fiber(data)),
                    Member(secondModel, Fiber(data))),
                Equal(
                    Apply(target, firstModel),
                    Apply(target, secondModel))));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, value, Colon, Sp, TypeUniverse(), Comma, Sp,
            NonemptyInstance(value), Comma, RowBreak, Grp(),
            target, Colon, Sp, Arrow(coupling, value), Comma, RowBreak, Grp(),
            IffFormula(factorization, fiberConstancy), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula FiberVariationFormula()
    {
        Formula marginalFamily = Arrow(F.Id("Bool"), F.Id("BooleanMarginal"));
        Formula coupling = F.Id("BooleanCoupling");
        Formula data = F.Id("mu");
        Formula firstModel = F.Id("M");
        Formula secondModel = F.Id("N");

        return Disp(new Formula.BindMany(
            FormulaQuantifier.Exists,
            [
                Bound("mu", marginalFamily),
                Bound("M", coupling),
                Bound("N", coupling),
            ],
            And(
                Member(firstModel, Fiber(data)),
                And(
                    Member(secondModel, Fiber(data)),
                    NotEqual(
                        Apply(F.Id("CF"), firstModel),
                        Apply(F.Id("CF"), secondModel))))));
    }

    private static Formula NonidentifiabilityFormula()
    {
        Formula marginalFamily = Arrow(F.Id("Bool"), F.Id("BooleanMarginal"));
        Formula counterfactualTable = Arrow(
            F.Id("Bool"),
            Arrow(F.Id("Bool"), Arrow(F.Id("Bool"), F.Id("Bool"))));
        Formula factor = F.Id("f");
        Formula factorType = Seq(
            Open, marginalFamily, Close, Sp, To, Sp, counterfactualTable);

        return Disp(new Formula.Not(new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("f", factorType)],
            Equal(
                F.Id("CF"),
                Seq(factor, Sp, Circ, Sp, F.Id("allSingleWorldMarginals"))))));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
}
