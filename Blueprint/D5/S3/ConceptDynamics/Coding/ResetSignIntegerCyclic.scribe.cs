using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class ResetSignIntegerCyclicDocument : IScribeDocumentDefinition
{
    private static Formula I(string name) => F.Id(name);
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula E(Formula a) => Call("ringEquiv", I("q"), a);
    private static Formula Inv(Formula a) => Call("inverse", Call("ringEquiv", I("q")), a);
    private static Formula PP(Formula a) => Call("pp", I("q"), a);
    private static Formula FP(Formula a) => Call("fp", I("q"), a);
    private static Formula Include(Formula a) => Call("inclusion", a);
    private static Formula Tau => PP(Call("C", I("resetLabel")));

    private static Formula Presentation()
    {
        Formula[] clauses = [
            Equal(Call("compose", Call("forward", I("q")), Call("backward", I("q"))),
                Call("ringIdentity", Call("QF", I("q")))),
            Equal(Call("compose", Call("backward", I("q")), Call("forward", I("q"))),
                Call("ringIdentity", Call("QP", I("q")))),
            All(Equal(E(PP(Include(I("p")))), FP(I("p"))), B("p", I("IntPolynomial"))),
            All(Equal(Inv(FP(I("p"))), PP(Include(I("p")))), B("p", I("IntPolynomial"))),
            Equal(E(PP(I("X"))), FP(I("X"))),
            Equal(E(Tau), FP(Call("W", I("q")))),
            All(Equal(E(PP(Call("C", Call("integerScalar", I("z"))))), FP(Call("C", I("z")))),
                B("z", I("Int"))),
            Equal(E(Num(1)), Num(1)),
            new Formula.Logic(Equal(I("q"), Num(1)), FormulaLogicOperator.Implies,
                Equal(E(Tau), FP(I("X"))))
        ];
        Formula body = clauses[^1];
        for (int i = clauses.Length - 2; i >= 0; i--) body = And(clauses[i], body);
        return All(body, B("q", I("Nat")));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal integral Sign elimination preserves forward time and both inverse maps.",
        H("The literal Sign ring quotient"),
        Blocks(
            Describe.Lean(DescribeId.Create("geometric"), DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/Coding/ResetSignIntegerCyclic.geometric"),
                H("The consumed geometric certificate"), StatementSource.FromAuthor(Disp(All(
                    Equal(Call("sub", Call("power", I("X"), I("q")),
                        Call("multiply", Call("sub", I("X"), Num(1)), Call("S", I("q")))), Num(1)),
                    B("q", I("Nat"))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This existing all-natural-q certificate is public for "
                    + "ResetIntegralGluing's actual ideal and coefficient-half reconstruction. "
                    + "The proof is reused unchanged and is a consumed helper."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sign-square"), DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/Coding/ResetSignIntegerCyclic.sign_square"),
                H("The consumed integral sign involution"), StatementSource.FromAuthor(Disp(All(
                    Equal(Call("multiply", FP(Call("W", I("q"))), FP(Call("W", I("q")))), Num(1)),
                    B("q", I("Nat"))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original sign certificate supplies the inverse of "
                    + "wUnit in ResetIntegralUnits. Its proof and scope are unchanged."))), DescribeRole.Theorem),
            Paragraph(Text("Sign is Multiplicative Bool, oddTau is ofAdd true, and the coefficient "
                + "ring R is literally MonoidAlgebra Int Sign. Its resetLabel is single oddTau 1 "
                + "from ResetNativeOddObstruction. Put S(q)=sum over k<q of X^k, "
                + "F(q)=X^(2q)-S(q)^2, and W(q)=S(q)-(X-1)*X^q. QP(q) is the accepted "
                + "FiniteCompanionCyclicModule.CyclicQ at R and resetLabel, hence R[X]/(P), "
                + "where P=X^q-C(resetLabel)*S(q). QF(q) is Int[X]/(F). pp and fp are their "
                + "canonical quotient ring maps; inclusion maps integer coefficients canonically "
                + "into R. No rational sign splitting, rank argument, or history equivariance "
                + "assumption is used.")),
            Describe.Lean(DescribeId.Create("literal-sign-integral-presentation"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/ResetSignIntegerCyclic.literal_presentation"),
                H("Actual inverse quotient maps and generator images"),
                StatementSource.FromAuthor(Disp(Presentation())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("compose is RingHom.comp and ringIdentity is RingHom.id. "
                    + "IntPolynomial means Polynomial Int. integerScalar is algebraMap Int R. "
                    + "inverse is the RingEquiv inverse. ringEquiv has forward as its actual "
                    + "forward map and backward as its actual inverse. Every natural q is included; "
                    + "the intended native consumer uses q>0. At q=1, S=1, F=X^2-1 and "
                    + "W-X=-F, so the literal sign class maps to the time class.")),
                    Paragraph(Text("The geometric identity X^q-(X-1)*S=1 yields the exact certificates "
                        + "X^q-W*S=F and W^2-1=((X-1)^2-1)*F. Thus [W]^2=1 in QF. "
                        + "signHom sends 1 to 1 and oddTau to [W], with multiplication proved "
                        + "by the actual two Sign cases. coefficientHom is MonoidAlgebra.lift of "
                        + "this monoid hom, and forwardPolynomial is Polynomial.eval2RingHom with "
                        + "X sent to [X]. The first certificate kills P, so the map descends. "
                        + "flip_twice 1 gives resetLabel^2=1. In the source ring, "
                        + "inclusion(F)=(X^q+C(resetLabel)*inclusion(S))*P and "
                        + "C(resetLabel)-inclusion(W)=(X-1+C(resetLabel))*P. The first kills F "
                        + "for backward=pp composed with inclusion; the second identifies the "
                        + "source coefficient. Quotient and polynomial ring-hom extensionality, "
                        + "then MonoidAlgebra.ringHom_ext on scalars and both Sign elements, "
                        + "prove the two inverse identities."))),
                DescribeRole.Theorem),
            Paragraph(Text("The next consumer is the actual integer-linear map from QF to "
                + "DimensionGroup(resetMatrix q), obtained through ringEquiv inverse, the accepted "
                + "arbitrary-ring cyclicEquiv at R/resetLabel, and resetNativeEquiv inverse. "
                + "It must prove that 1 is stage-zero e0 and X intertwines original resetTheta, "
                + "then use LinearEquiv.ofAEval for the Int[X]-module chart. Native stage n uses "
                + "inverse time powers. Transferring oddTau=W(Theta) additionally requires the "
                + "concrete coefficient law for groupAction, resetNativeEquiv_stage and "
                + "DirectLimit.map_apply_of; integer linearity alone is insufficient. This module "
                + "proves no native chart, square range/image correspondence, four oriented branches, "
                + "exact resetFiveClock, centralizer/units, or full original rho character/action. "
                + "The result is a repository derivation using the standard group-algebra and "
                + "polynomial universal properties, without a claim of literature novelty.")))));
}
