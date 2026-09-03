using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Causal;

internal sealed class FiniteEventCouplingSharpBoundsDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Causal/FiniteEventCouplingSharpBounds.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A two-event coupling polytope has an explicit primal witness, replayable "
            + "dual-slack certificate, and exact sharp projection bounds.",
        H("Finite Event Coupling Sharp Bounds"),
        Blocks(
            Paragraph(Text(
                "The feasible object is a normalized nonnegative law on two Boolean "
                    + "event indicators with two prescribed marginals. Its target "
                    + "coordinate is the true-true intersection cell.")),
            Paragraph(Text(
                "Normalization and the two marginal rows produce exact slack identities "
                    + "for the Fréchet lower plane and the two upper planes. An additional "
                    + "linear cap on disagreement contributes a fourth lower plane.")),
            Paragraph(Text(
                "The explicit four-cell coupling realizes every target in the resulting "
                    + "closed interval. The necessity proof replays the certificate, while "
                    + "the sufficiency proof constructs the primal witness.")),
            Describe.Lean(
                DescribeId.Create("event-coupling-dual-certificate"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "event_coupling_dual_certificate"),
                H("Marginal rows generate a replayable dual-slack certificate"),
                StatementSource.FromAuthor(CertificateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every feasible coupling and every proposed disagreement cap, "
                        + "the four exact slack identities hold. Nonnegativity and the cap "
                        + "can then be checked separately when the certificate is replayed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "event-coupling-target-feasible-with-disagreement-cap-iff"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "event_coupling_target_feasible_with_disagreement_cap_iff"),
                H("The disagreement-constrained interval is exactly sharp"),
                StatementSource.FromAuthor(SharpFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A real target lies in the displayed interval exactly when some "
                        + "normalized nonnegative coupling has the required marginals, "
                        + "obeys the disagreement cap, and realizes that target."))),
                DescribeRole.Theorem))));

    private static Formula CertificateFormula()
    {
        Formula realType = F.Id("Real");
        Formula pairType = Call("Prod", F.Id("Bool"), F.Id("Bool"));
        Formula mass = F.Id("mass");
        Formula left = F.Id("leftMarginal");
        Formula right = F.Id("rightMarginal");
        Formula cap = F.Id("disagreementCap");
        Formula massType = new Formula.TypeArrow(pairType, realType);
        Formula feasible = Call("IsEventCoupling", mass, left, right);
        Formula certificate =
            Call("EventCouplingDualCertificate", mass, left, right, cap);

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("mass", massType),
                Bound("leftMarginal", realType),
                Bound("rightMarginal", realType),
                Bound("disagreementCap", realType),
            ],
            Implies(feasible, certificate)));
    }

    private static Formula SharpFormula()
    {
        Formula realType = F.Id("Real");
        Formula pairType = Call("Prod", F.Id("Bool"), F.Id("Bool"));
        Formula mass = F.Id("mass");
        Formula left = F.Id("leftMarginal");
        Formula right = F.Id("rightMarginal");
        Formula cap = F.Id("disagreementCap");
        Formula target = F.Id("target");
        Formula zero = new Formula.Number(0);
        Formula one = new Formula.Number(1);
        Formula two = new Formula.Number(2);

        Formula marginalSum = Add(left, right);
        Formula frechetPlane = Subtract(marginalSum, one);
        Formula disagreementPlane =
            new Formula.Fraction(Subtract(marginalSum, cap), two);
        Formula lower = Call(
            "max",
            Call("max", zero, frechetPlane),
            disagreementPlane);
        Formula upper = Call("min", left, right);
        Formula interval = And(
            Relation(lower, FormulaRelationOperator.LessThanOrEqual, target),
            Relation(target, FormulaRelationOperator.LessThanOrEqual, upper));

        Formula targetCell = Apply(
            mass,
            Pair(F.Id("true"), F.Id("true")));
        Formula witnessConditions = And(
            Call("IsEventCoupling", mass, left, right),
            And(
                Relation(
                    Call("disagreementMass", mass),
                    FormulaRelationOperator.LessThanOrEqual,
                    cap),
                Equal(targetCell, target)));
        Formula witness = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("mass", new Formula.TypeArrow(pairType, realType))],
            witnessConditions);

        Formula equivalence =
            new Formula.Logic(interval, FormulaLogicOperator.Iff, witness);

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("leftMarginal", realType),
                Bound("rightMarginal", realType),
                Bound("disagreementCap", realType),
                Bound("target", realType),
            ],
            equivalence));
    }

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Pair(Formula first, Formula second) =>
        Call("pair", first, second);

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
