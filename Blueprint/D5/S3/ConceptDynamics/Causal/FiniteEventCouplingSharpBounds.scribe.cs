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
            Paragraph(Text(
                "Theorem 18.1 of AURIC_FIB_ATOM_JOINT_PROJECTION_MULTIWINDOW_ORDER_AND_RESPONSE_FIBERS (source part "
                    + "II, section 6) concerns two laws on the original LiteralWindowEnd.Window. Let mu and nu be arbitrary "
                    + "nonnegative real masses, each summing to one on all five letters, including zero. Put A(i)=first(i), "
                    + "B(j)=last(j), a=mu(low)+mu(ends) and b=nu(high)+nu(ends). The source sets R1={low,ends} and "
                    + "C1={high,ends} are exactly their true fibers; R0 and C0 are the full complements. One nonnegative "
                    + "table P on Window x Window has every row sum mu(i), every column sum nu(j), and P(i,j)=0 whenever "
                    + "A(i)&&B(j), if and only if a+b<=1.")),
            Paragraph(Text(
                "Push P forward along (i,j) -> (A(i),B(j)). This is an IsEventCoupling with leftMarginal=a, "
                    + "rightMarginal=b and true-true cell zero. Conversely event_coupling_target_feasible_iff(a,b,0) "
                    + "reduces, using 0<=a,b<=1, exactly to a+b<=1. Its Boolean witness q has masses (1-a-b,a,b,0) in the "
                    + "order (false,false), (true,false), (false,true), (true,true). This supplies the event table; "
                    + "recovering the original marginals also requires the conditional lift.")),
            Paragraph(Text(
                "Form piMu(r,i)=mu(i) when A(i)=r and zero otherwise, and the analogous piNu(s,j) for B. Their "
                    + "Boolean marginals are alpha=(1-a,a) and beta=(1-b,b). TreeMarkovStability.completedConditional gives "
                    + "kernels Kmu and Knu using fallback laws mu and nu. The existing private "
                    + "completed_conditional_properties supplies nonnegativity, unit row sums and "
                    + "alpha(r)*Kmu(r,i)=piMu(r,i), with the analogous identity for nu. Extend q by these two kernels, then "
                    + "discard the Boolean labels: P(i,j)=sum over r,s of q(r,s)*Kmu(r,i)*Knu(s,j). The existing private "
                    + "extend_marginals and PushforwardComposition.pushforward_comp recover all row and column masses. On "
                    + "positive Boolean fibers the kernels are supported on their graph; on zero fibers the existing "
                    + "private zero_fiber forces the whole q fiber to vanish. Thus the pushforward returns q, and "
                    + "nonnegativity makes its true-true cell zero equivalent to every cell in R1 x C1 being zero. This "
                    + "application preserves private visibility.")),
            Paragraph(Text(
                "For a,b<1 this is the source's table: mu(i)*nu(j)/(1-b) on R1 x C0, mu(i)*nu(j)/(1-a) on R0 x C1, "
                    + "(1-a-b)*mu(i)*nu(j)/((1-a)*(1-b)) on R0 x C0, and zero on R1 x C1. When a+b=1 with a,b<1 the R0 x C0 "
                    + "block vanishes. At a=1 feasibility forces b=0, and the product mu(i)*nu(j) on R1 x C0, zero "
                    + "elsewhere, suffices; b=1 is symmetric on R0 x C1. No division by zero is used. Zero coordinates, "
                    + "deterministic laws and null windows remain included.")),
            Paragraph(Text(
                "The source reads HIGH-to-LOW: the first window's low bit meets the second window's high bit. "
                    + "ImmediateWindowStateCapacity.rawTransition from its initial some(false,0) state records first(i), "
                    + "then rejects j exactly when first(i)&&last(j); none is absorbing. This is the raw transition guard; "
                    + "LiteralWindowEnd.execution uses the opposite low-to-high order. The application proves no End "
                    + "acceptance, unique joint law, maximum-entropy characterization, physical implementation, sampling "
                    + "procedure or resource bound, and does not settle the adjacent cycle-dimension claim. It reuses "
                    + "existing frozen results without a new Lean declaration.")),
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
