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
            Paragraph(Text(
                "For a five-mode Fibonacci window law p on null, low 2, high 5, ends 25 and middle 3, "
                    + "all cell masses are real, nonnegative and sum to one. Set X=p(low)+p(ends), "
                    + "Y=p(high)+p(ends), Z=p(middle), r=1-Z and kappa=p(ends). "
                    + "The endpoint and middle occupancy coordinates satisfy X,Y,Z>=0, X+Z<=1 and Y+Z<=1. "
                    + "PathStableSetPolytope.convexHull_three_pyramid applies in coordinate order (X,Z,Y), "
                    + "identifying this domain with the convex hull of the five admissible three-bit words.")),
            Paragraph(Text(
                "The full fixed-coordinate family has cells (r-X-Y+kappa, X-kappa, Y-kappa, kappa, Z). "
                    + "Nonnegativity is exactly max(0,X+Y-r)<=kappa<=min(X,Y), together with Z>=0. "
                    + "Every coarse point is feasible: the lower endpoint lies below both X and Y. "
                    + "When r>0, divide the four bottom cells by r and apply event_coupling_primal_bounds "
                    + "and event_coupling_target_feasible_iff with left marginal X/r, right marginal Y/r "
                    + "and intersection kappa/r. Rescaling gives the complete sharp interval, including its "
                    + "zero-cell endpoints. Its length is w=min(X,Y,r-X,r-Y); a zero length gives a singleton, "
                    + "and a positive length gives distinct laws with identical coarse coordinates.")),
            Paragraph(Text(
                "The bottom determinant is Delta=p(null)p(ends)-p(low)p(high)=r*kappa-X*Y. "
                    + "For r>0 it recovers kappa=(X*Y+Delta)/r and hence all five cells. "
                    + "CrossWorldIndependenceSharpBounds.independent_joint_event_eq_product applies to the "
                    + "normalized bottom table. Delta=0 is equivalent to factorization of all four conditional "
                    + "cells into their Boolean marginal products. Conversely eventCoupling_isIndependent "
                    + "supplies the product completion kappa*=X*Y/r, which remains a legal five-mode law. "
                    + "This concerns independence given the middle is absent. It is not unconditional "
                    + "endpoint independence when Z is positive: at X=Y=2/5, Z=1/5, kappa=1/5, Delta=0 "
                    + "but kappa differs from X*Y. At r=0 nonnegativity forces the unique middle law, "
                    + "with X=Y=kappa=0; no division by r is used.")),
            Paragraph(Text(
                "For any real target f on the same five letters, Jf=f(ends)-f(low)-f(high)+f(null). "
                    + "Its expectation is (r-X-Y)f(null)+X*f(low)+Y*f(high)+Z*f(middle)+Jf*kappa. "
                    + "Thus its difference from the product completion is Jf*Delta/r only for r>0. "
                    + "The target image of the full kappa interval is the unordered closed interval between "
                    + "its endpoint expectations, by Mathlib Set.image_const_mul_uIcc and "
                    + "Set.image_const_add_uIcc. Its width is abs(Jf)*w, with no sign restriction on Jf. "
                    + "At the apex the expectation is f(middle). The parameter f specifies the mathematical "
                    + "target; it defines no aggregate score or acquisition rule. The coupling bounds and "
                    + "affine interval-image identities establish these consequences by normalization.")),
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
