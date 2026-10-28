using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class OriginalDensityStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strong derivative error and a separate terminal phase certificate control the full original output.",
        H("Loss density stability on the original clock"), Blocks(
            Paragraph(Text("Let c<1/2, 0<a<c and eta>0. Both (k,chi) and (l,psi) are original controls at the same base (c,c,1-2c) and horizon T>=0, with k(0)=l(0)=a. Both heights stay in [eta,c-eta]. For every t in [0,T], assume |k(t)-l(t)|<=delta. All integrals are Lebesgue integrals on (0,T], with their norm taken before integration. The original regularity alternatives imply absolute continuity and integrability of the derivatives; no common partition or derivative supremum bound is assumed.")),
            Paragraph(Text("Write e=derivativeError(T,k,l)=integral |k prime-l prime|, M=variation(T,l)=integral |l prime|, and D=variation(T,k)=integral |k prime|. Absolute continuity identifies these variations with total variation. Define budget(eta,delta,e,M)=B=e/eta+M delta/eta^2. The five original probabilities have slopes sigma=(1,-1,0,-1,1), in mode order 0,1,2,3,13. Every mode remains in the loss output, including constant-probability mode 2 and mode 13 at index four.")),
            Entry("hazard-pointwise", "hazard_pointwise_error", "Pointwise hazard error",
                Statement("hazard_pointwise_error"),
                "For any two differentiable-value functions k,l and any real t at which both heights lie in [eta,c-eta], |hazard_k(t)-hazard_l(t)|<=|k prime(t)-l prime(t)|/eta+|l prime(t)| |k(t)-l(t)|/eta^2. The assertion is pointwise for totalized derivatives. The velocity dependence is continuous piecewise linear, and changing a reciprocal height costs at most the height error divided by eta squared."),
            Entry("hazard-integral", "hazard_integral_error", "Accumulated hazard error",
                Statement("hazard_integral_error"),
                "Under the common margin and height-error hypotheses, integral_0^T |hazard_k-hazard_l|<=B. The proof integrates the pointwise bound using the actual L1 derivative difference and the variation of l."),
            Entry("survival-integral", "survival_integral_error", "Every survival prefix uses the full hazard error",
                Statement("survival_integral_error"),
                "For any two original controls and every t in [0,T], |S_k(t)-S_l(t)|<=integral_0^T |hazard_k-hazard_l|. No margin hypothesis is needed for this intermediate assertion. The hazard primitives are nonnegative; exp(-x) is one-Lipschitz for x>=0."),
            Entry("survival-budget", "survival_error", "Uniform survival error",
                Statement("survival_error"),
                "The accumulated hazard estimate therefore gives |S_k(t)-S_l(t)|<=B for every t in [0,T] under the common margin and height-error assumptions."),
            Entry("loss-density", "loss_density_error", "The exact loss-density estimate IS.28",
                Statement("loss_density_error"),
                "For every original mode i, integral_0^T |lossDensity_i(k)-lossDensity_i(l)|<=(1+M/eta+D)B+delta+e. lossDensity_i is the original unnormalized source-family density, modeCoefficient_i p_i(a); OriginalReferenceOutputMeasure.source_coefficient identifies it with the source failureDensity, and native_coefficient_deriv identifies it almost everywhere with minus the derivative of S p_i(k). No common initial-height equality is needed for this scalar estimate itself."),
            Paragraph(Text("Product differentiation gives the four differences -(S_k prime-S_l prime)p_i(k), -S_l prime(p_i(k)-p_i(l)), -(S_k-S_l)sigma_i k prime, and -S_l sigma_i(k prime-l prime). Their integrated absolute values are bounded by (1+M/eta)B, delta, DB and e. Here integral |S_k prime-S_l prime|<=(1+M/eta)B follows from S prime=-hazard S and integral hazard_l<=M/eta. Monotone survival gives integral |S_l prime|=1-S_l(T)<=1. Each p_i is at most one, each probability coordinate is one-Lipschitz, and |sigma_i|<=1. This proves the displayed constants for all five modes.")),
            Entry("variation-bound", "variation_le", "No additional speed hypothesis is required",
                Statement("variation_le"),
                "For every two original controls on the same horizon, D<=M+e follows by integrating |k prime|<=|l prime|+|k prime-l prime|. The variations are the integrals of the derivatives of the actual absolutely continuous heights."),
            Entry("combined-bound", "complete_error_bound", "The full complete-output estimate",
                Statement("complete_error_bound"),
                "Put d_min=initialFloor(c,a)=min(a,c-a,1-2c)>0 and C=(1+M/eta+D)B+delta+e. For the actual complete operational distance of OriginalCompleteOutputStability, d_op<=sqrt((B+delta)/d_min)+phaseError+C/(2 d_min). phaseError=max_i |character_i(k,chi,T)-character_i(l,psi,T)| is a separate terminal character certificate. In the display, rootBudget=sqrt((B+delta)/d_min) and densityBudget=C/(2 d_min). The result combines the complete joint-output estimate IS.27, the loss-density estimate IS.28 and the terminal Kraus estimate IS.29, on the same common data."),
            Entry("height-from-derivatives", "height_error_le_derivativeError", "A common initial height gives uniform height control",
                Statement("height_error_le_derivativeError"),
                "For any two original controls with k(0)=l(0), and every t in [0,T], |k(t)-l(t)|<=derivativeError(T,k,l). The fundamental theorem for absolutely continuous functions writes the difference as the integral of k prime-l prime on (0,t], which is bounded by the full L1 difference."),
            Entry("complete-convergence", "complete_output_convergence", "Convergence of the complete operational output",
                Statement("complete_output_convergence"),
                "Fix c,a,T,eta and a real bound M. Let (k_n,chi_n) and (l_n,psi_n) be two sequences of original controls on the common base and horizon, with both initial heights a and both heights in [eta,c-eta] for every n. Assume variation(T,l_n)<=M for every n, derivativeError(T,k_n,l_n) tends to zero, and phaseError(c,T,k_n,chi_n,l_n,psi_n) separately tends to zero. Then their completeOperationalDistance tends to zero, uniformly over all normalized positive joint trace-class inputs and unchanged Hilbert references in any fixed universe."),
            Paragraph(Text("For convergence take delta_n=e_n, use D_n<=M+e_n and B_n=e_n/eta+M e_n/eta^2. The common initial probability floor is strictly positive. Continuity of the square root and the rational polynomial upper bound makes every term in the combined estimate tend to zero. Nonnegativity of the actual operational distance completes the squeeze argument. This proves a sufficient condition; it asserts neither necessity of derivative convergence nor acquisition of the phase certificate.")),
            Paragraph(Text("The actual output is the successful tensor Kraus congruence together with five Bochner failure-density measures on the same reference and physical time records. The result does not infer terminal phase control from height control, recover an intermediate phase waveform, grant access to old programme fields, construct an acquisition service, authorize a post-failure restart or establish physical realization.")))));

    private static DocumentBlock Entry(string id, string declaration, string title, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Quantum/Fibers/OriginalDensityStability." + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);


    private static Formula I(string n) => F.Id(n);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a,op,b);
    private static Formula E(Formula a, Formula b) => Rel(a,FormulaRelationOperator.Equal,b);
    private static Formula L(Formula a, Formula b) => Rel(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula A(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.And,b);
    private static Formula P(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula.BoundVariable V(string n, Formula t) => new(FormulaIdentifier.Create(n),t);
    private static Formula Q(string reals, string paths, Formula premise, Formula result, params Formula.BoundVariable[] extra)
    {
        Formula r=I("Real");
        var vs=new List<Formula.BoundVariable>();
        if(reals != "") vs.AddRange(reals.Split(' ').Select(n=>V(n,r)));
        if(paths != "") vs.AddRange(paths.Split(' ').Select(n=>V(n,C("Function",r,r))));
        vs.AddRange(extra);
        return new Formula.BindMany(FormulaQuantifier.ForAll,[..vs],P(premise,result));
    }
    private static Formula Original(Formula c,Formula t,Formula k,Formula chi) => C("OriginalControl",C("base",c),t,k,chi);
    private static Formula Pair(Formula c,Formula t,Formula k,Formula chi,Formula l,Formula psi) =>
        A(Original(c,t,k,chi),Original(c,t,l,psi));
    private static Formula Common(Formula c,Formula a,Formula t,Formula k,Formula chi,Formula l,Formula psi) =>
        A(C("cLessHalf",c),A(C("initialInterior",a,c),A(Pair(c,t,k,chi,l,psi),
            A(E(C("evaluate",k,D(0)),a),E(C("evaluate",l,D(0)),a)))));

    private static Formula Statement(string name)
    {
        Formula c=I("c"),a=I("a"),t=I("T"),eta=I("eta"),delta=I("delta"),
            k=I("k"),chi=I("chi"),l=I("l"),psi=I("psi"),u=I("t"),i=I("i");
        Formula pair=Pair(c,t,k,chi,l,psi),margin=C("uniformPairMargin",t,eta,c,k,l),
            positive=C("positive",eta),height=C("uniformHeightErrorLe",t,k,l,delta);
        Formula error=C("derivativeError",t,k,l),m=C("variation",t,l),d=C("variation",t,k);
        Formula budget=C("budget",eta,delta,error,m),surv=C("absSurvivalDifference",c,k,l,u),
            hazard=C("integralAbsHazardDifference",c,t,k,l);
        Formula hypotheses=A(positive,A(pair,A(margin,height)));
        Formula common=Common(c,a,t,k,chi,l,psi);
        return name switch
        {
            "hazard_pointwise_error" => Q("c eta t","k l",A(positive,C("pointwisePairMargin",u,eta,c,k,l)),
                L(C("absHazardDifference",c,k,l,u),Seq(C("absDerivativeDifference",k,l,u),Slash,eta,Plus,
                    C("absDerivative",l,u),C("absHeightDifference",k,l,u),Slash,C("square",eta)))),
            "hazard_integral_error" => Q("c T eta delta","k chi l psi",hypotheses,L(hazard,budget)),
            "survival_integral_error" => Q("c T t","k chi l psi",A(pair,C("inIcc",u,D(0),t)),L(surv,hazard)),
            "survival_error" => Q("c T eta delta t","k chi l psi",A(hypotheses,C("inIcc",u,D(0),t)),L(surv,budget)),
            "loss_density_error" => Q("c a T eta delta","k chi l psi",A(C("cLessHalf",c),A(C("initialInterior",a,c),hypotheses)),
                L(C("integralAbsLossDensityDifference",c,a,t,k,l,i),Seq(Open,D(1),Plus,m,Slash,eta,Plus,d,Close,budget,Plus,delta,Plus,error)),V("i",I("FinFive"))),
            "variation_le" => Q("c T","k chi l psi",pair,L(d,Seq(m,Plus,error))),
            "complete_error_bound" => Q("c a T eta delta","k chi l psi",A(common,A(positive,A(margin,height))),
                L(C("completeOperationalDistance",c,a,t,k,chi,l,psi),Seq(C("rootBudget",c,a,budget,delta),Plus,C("phaseError",c,t,k,chi,l,psi),Plus,C("densityBudget",c,a,eta,delta,error,m,d,budget)))),
            "height_error_le_derivativeError" => Q("c T t","k chi l psi",A(pair,A(E(C("evaluate",k,D(0)),C("evaluate",l,D(0))),C("inIcc",u,D(0),t))),L(C("absHeightDifference",k,l,u),error)),
            "complete_output_convergence" => Convergence(),
            _ => throw new InvalidOperationException(name)
        };
    }
    private static Formula Convergence()
    {
        Formula c=I("c"),a=I("a"),t=I("T"),eta=I("eta"),m=I("M"),k=I("k"),chi=I("chi"),l=I("l"),psi=I("psi");
        Formula r=I("Real"),seq=C("Sequence",C("Function",r,r));
        Formula premise=A(C("cLessHalf",c),A(C("initialInterior",a,c),A(C("positive",eta),
            A(C("allCommonOriginalControls",c,a,t,k,chi,l,psi),A(C("allUniformPairMargins",t,eta,c,k,l),
            A(C("allVariationLe",t,l,m),A(C("derivativeErrorsTendstoZero",t,k,l),C("terminalPhaseErrorsTendstoZero",c,t,k,chi,l,psi))))))));
        return new Formula.BindMany(FormulaQuantifier.ForAll,[V("c",r),V("a",r),V("T",r),V("eta",r),V("M",r),V("k",seq),V("chi",seq),V("l",seq),V("psi",seq)],
            P(premise,C("completeOperationalDistancesTendstoZero",c,a,t,k,chi,l,psi)));
    }

    private static Formula C(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) items.Add(Comma);
            items.Add(arguments[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
