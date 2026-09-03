using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Causal;

internal sealed class TernaryTreatmentOutcomeSharpBoundsDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Causal/TernaryTreatmentOutcomeSharpBounds.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A three-level treatment, three-level outcome structural response model has "
            + "closed-form sharp bounds with primal and dual witnesses.",
        H("Ternary Treatment and Outcome Sharp Bounds"),
        Blocks(
            Paragraph(Text(
                "The exogenous response type has four states. Its first bit records "
                    + "whether treatment zero produces outcome zero, and its second bit "
                    + "records whether treatment two produces outcome two.")),
            Paragraph(Text(
                "Treatment one produces the neutral outcome one. The endpoint joint "
                    + "counterfactual query is therefore the true-true response cell, "
                    + "while the two endpoint interventional probabilities are its "
                    + "Boolean marginals.")),
            Paragraph(Text(
                "A cap on endpoint disagreement is a linear cross-world dependence "
                    + "restriction. The generic finite coupling theorem supplies both "
                    + "the dual certificate and an exogenous law attaining every point "
                    + "of the interval.")),
            Describe.Lean(
                DescribeId.Create("endpoint-model-dual-certificate"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "endpoint_model_dual_certificate"),
                H("The ternary endpoint model inherits the coupling certificate"),
                StatementSource.FromAuthor(CertificateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every endpoint model unfolds to a feasible two-event coupling plus "
                        + "the disagreement constraint. Its marginal rows therefore carry "
                        + "the same exact dual-slack certificate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ternary-endpoint-joint-query-sharp-iff"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "ternary_endpoint_joint_query_sharp_iff"),
                H("The ternary endpoint joint query has an exact sharp interval"),
                StatementSource.FromAuthor(SharpFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The displayed interval is necessary by certificate replay and "
                        + "sufficient by an explicit four-state exogenous response law. "
                        + "Both endpoints and every interior value are attained."))),
                DescribeRole.Theorem))));

    private static Formula CertificateFormula()
    {
        Formula realType = F.Id("Real");
        Formula responseType = F.Id("ResponseType");
        Formula mass = F.Id("mass");
        Formula zeroMarginal = F.Id("zeroTargetMarginal");
        Formula twoMarginal = F.Id("twoTargetMarginal");
        Formula cap = F.Id("disagreementCap");
        Formula massType = new Formula.TypeArrow(responseType, realType);
        Formula model =
            Call("IsEndpointModel", mass, zeroMarginal, twoMarginal, cap);
        Formula certificate = Call(
            "EventCouplingDualCertificate",
            mass,
            zeroMarginal,
            twoMarginal,
            cap);

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("mass", massType),
                Bound("zeroTargetMarginal", realType),
                Bound("twoTargetMarginal", realType),
                Bound("disagreementCap", realType),
            ],
            Implies(model, certificate)));
    }

    private static Formula SharpFormula()
    {
        Formula realType = F.Id("Real");
        Formula responseType = F.Id("ResponseType");
        Formula mass = F.Id("mass");
        Formula zeroMarginal = F.Id("zeroTargetMarginal");
        Formula twoMarginal = F.Id("twoTargetMarginal");
        Formula cap = F.Id("disagreementCap");
        Formula target = F.Id("target");
        Formula zero = new Formula.Number(0);
        Formula one = new Formula.Number(1);
        Formula two = new Formula.Number(2);

        Formula marginalSum = Add(zeroMarginal, twoMarginal);
        Formula frechetPlane = Subtract(marginalSum, one);
        Formula disagreementPlane =
            new Formula.Fraction(Subtract(marginalSum, cap), two);
        Formula lower = Call(
            "max",
            Call("max", zero, frechetPlane),
            disagreementPlane);
        Formula upper = Call("min", zeroMarginal, twoMarginal);
        Formula interval = And(
            Relation(lower, FormulaRelationOperator.LessThanOrEqual, target),
            Relation(target, FormulaRelationOperator.LessThanOrEqual, upper));

        Formula model =
            Call("IsEndpointModel", mass, zeroMarginal, twoMarginal, cap);
        Formula targetEquation =
            Equal(Call("endpointJointQuery", mass), target);
        Formula witness = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("mass", new Formula.TypeArrow(responseType, realType))],
            And(model, targetEquation));

        Formula equivalence =
            new Formula.Logic(interval, FormulaLogicOperator.Iff, witness);

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("zeroTargetMarginal", realType),
                Bound("twoTargetMarginal", realType),
                Bound("disagreementCap", realType),
                Bound("target", realType),
            ],
            equivalence));
    }

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Relation(
        Formula left,
        FormulaRelationOperator relation,
        Formula right) => new Formula.Relation(left, relation, right);

    private static Formula Implies(Formula hypothesis, Formula conclusion) =>
        new Formula.Logic(hypothesis, FormulaLogicOperator.Implies, conclusion);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
}
