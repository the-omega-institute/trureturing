using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class OriginalCompleteOutputStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stability of the complete original instrument on a common arbitrary reference.",
        H("The terminal quantum output and the full time record"), Blocks(
            Paragraph(Text("Fix c<1/2, 0<a<c, T>=0 and two original controls (k,chi) and (l,psi) at base (c,c,1-2c), with k(0)=l(0)=a. Both original regularity alternatives are included. The five probabilities, in the original order 0,1,2,3,13, are p(k)=(k,c-k,1-2c,c-k,k). S_k(t)=exp(-integral_0^t hazard(c,k,u) du) is the native survival. All integrals use the same physical time coordinate and Lebesgue measure.")),
            Paragraph(Text("The character z_i(t)=exp(-I integral_0^t phaseWeight((c,c,1-2c),k(u),i) chi prime(u) du) retains the original real phase integral. terminalDiagonal_i(t)=sqrt(S_k(t)) sqrt(p_i(k(t))/p_i(a)) z_i(t), and terminalKraus is its diagonal action on Blocks(Fin5,H). The existing tensor_diagonal identity identifies this action with the system Kraus map tensored with the identity on H. H is any complete complex Hilbert space; separability and product-state assumptions are absent.")),
            Paragraph(Text("For a common positive trace-class rho on Blocks(Fin5,H), terminalOutput is the actual terminalKraus rho terminalKraus-adjoint. phasedJump_i is the literal absorbing jump composed with the transported character diagonal. phasedFailure is its actual trace-class congruence, taking values in Blocks(Fin6,H), with absorbing coordinate f=5. completeDistance is one half of the sum of the terminal output difference norm and, over all five modes, the time integral of the norm of the density difference. The norm is taken before integrating time. Thus arbitrary Borel time events and the unchanged reference are retained.")),
            Entry("height-control", "height_control", "The height retains original admissibility",
                Statement("height_control"),
                "For any original (k,chi), replacing chi by the constant zero function gives an original control on the same base and horizon. Absolute continuity of k follows from either original regularity alternative. This permits direct use of the existing native mode balance theorem without changing k or its clock."),
            Entry("phased-failure", "phased_failure_actual", "The failure congruence is phase independent",
                Statement("phased_failure_actual"),
                "For every real c,a,t, every k,chi, every original mode i and every positive trace-class rho on the same Blocks(Fin5,H), liveFailure_i(t) equals phasedJump_i(t) rho phasedJump_i(t)-adjoint. The jump row has one nonzero coordinate, so composing with the diagonal multiplies it by z_i(t). The character has modulus one and cancels inside the congruence. The terminal phase remains in terminalOutput."),
            Entry("mode-contraction", "native_mass_le", "Each surviving mode is a contraction",
                Statement("native_mass_le"),
                "For every t in [0,T] and i in Fin5, native mode balance and nonnegativity of the integrated squared jump amplitude give S_k(t)p_i(k(t))<=p_i(a). Consequently every successful diagonal entry has modulus at most one. The assertion uses the common initial height; survival<=1 alone would not establish this contraction."),
            Entry("joint-bound", "complete_output_bound", "The complete distance for any common positive joint input",
                Statement("complete_output_bound"),
                "For every arbitrary H and positive trace-class rho, and every real b with densityError_i<=b for all i, completeDistance<= (krausError+b/2) norm(rho). Here lossDensity_i=modeCoefficient_i p_i(a), densityError_i=integral_0^T |lossDensity_i(k)-lossDensity_i(l)|/p_i(a), and krausError is the operator norm of the difference of the actual terminal Kraus maps on the original five-dimensional system. The result is unnormalized and retains entangled inputs."),
            Entry("operational-bound", "complete_operational_bound", "The operational estimate IS.27",
                Statement("complete_operational_bound"),
                "completeOperationalDistance is the supremum of completeDistance over all complete complex Hilbert references in any fixed universe and all positive joint trace-class inputs of trace norm one. The joint-input estimate gives d_op<=kappa+(max_i densityError_i)/2, with exactly the coefficient one on kappa. A one-dimensional reference embedded in a live coordinate proves the set of inputs is nonempty."),
            Entry("operational-positive", "complete_operational_nonneg", "The operational distance is nonnegative",
                Statement("complete_operational_nonneg"),
                "Under the same common initial-height and original-control hypotheses, the operational supremum is bounded above and contains the distance of a normalized live input. Each norm integral is nonnegative, so d_op>=0. This supplies the lower bound for convergence by squeezing."),
            Entry("survival-unit", "survival_le_one", "Survival never exceeds one",
                Statement("survival_le_one"),
                "For every original (k,chi) and every t in [0,T], S_k(t)<=1. Native bounds put the height strictly between zero and c, so each term in its hazard is nonnegative."),
            Entry("probability-unit", "probability_le_one", "Every original probability is at most one",
                Statement("probability_le_one"),
                "For c<1/2, 0<x<c and every mode i, positivity and the original probability sum give p_i(x)<=1."),
            Entry("probability-difference", "probability_difference", "Every probability coordinate is nonexpansive",
                Statement("probability_difference"),
                "For arbitrary real c,x,y and all five original modes, |p_i(x)-p_i(y)|<=|x-y|. Their slopes are 1,-1,0,-1,1, including the constant mode 2 and mode 13 at index four."),
            Entry("terminal-bound", "terminal_error_bound", "The terminal amplitude and character estimate IS.29",
                Statement("terminal_error_bound"),
                "In addition to the common control hypotheses, suppose |S_k(T)-S_l(T)|<=B and |k(T)-l(T)|<=delta. Then kappa<=max_i sqrt((B+delta)/p_i(a))+max_i |z_i(T)-w_i(T)|. The terminal phase error is an independent certificate. The amplitude difference uses |S_k p_i(k)-S_l p_i(l)|<=B+delta and the square-root inequality |sqrt(x)-sqrt(y)|<=sqrt(|x-y|). Contractivity bounds the coefficient of the character difference by one."),
            Paragraph(Text("The terminal proof writes A rho A-adjoint minus B rho B-adjoint as (A-B) rho A-adjoint plus B rho (A-B)-adjoint. The general trace-class ideal estimate bounds both mixed products, including nonpositive products, by their operator norms times norm(rho). The diagonal amplification bound holds on arbitrary H. The failure contribution is exactly sum_i densityError_i norm(rho_ii), where rho_ii is the compression of that same rho. Positivity is used only for these diagonal blocks and their trace partition sum_i norm(rho_ii)=norm(rho).")),
            Paragraph(Text("Terminal characters are not recovered from height data. No relative phase waveform, phase unwrapping, acquisition service, restart permission, physical realization or full programme reconstruction follows from these estimates.")))));

    private static DocumentBlock Entry(string id, string declaration, string title, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Quantum/Fibers/OriginalCompleteOutputStability." + declaration),
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
        Formula c=I("c"),a=I("a"),t=I("T"),k=I("k"),chi=I("chi"),l=I("l"),psi=I("psi"),
            u=I("t"),i=I("i"),rho=I("rho"),b=I("b"),budget=I("B"),delta=I("delta");
        Formula common=Common(c,a,t,k,chi,l,psi), pair=Pair(c,t,k,chi,l,psi);
        Formula mass=C("survivingModeMass",c,k,u,i),initial=C("p",c,a,i);
        Formula op=C("completeOperationalDistance",c,a,t,k,chi,l,psi);
        Formula kap=C("krausError",c,a,t,k,chi,l,psi);
        Formula mode=I("FinFive"),h=I("H");
        Formula.BoundVariable[] quantum=[V("H",I("CompleteComplexHilbertSpace")),V("rho",C("TraceClass",C("Blocks",mode,h)))];
        return name switch
        {
            "height_control" => Q("c T","k chi",Original(c,t,k,chi),Original(c,t,k,C("zeroFunction"))),
            "phased_failure_actual" => Q("c a t","k chi",C("Positive",rho),
                E(C("liveFailureOperator",c,a,k,i,rho,u),C("phasedKrausCongruence",c,a,k,chi,u,i,rho)),
                [..quantum,V("i",mode)]),
            "native_mass_le" => Q("c a T t","k chi",A(C("cLessHalf",c),A(C("initialInterior",a,c),
                A(Original(c,t,k,chi),A(E(C("evaluate",k,D(0)),a),C("inIcc",u,D(0),t))))),
                L(mass,initial),V("i",mode)),
            "complete_output_bound" => Q("c a T b","k chi l psi",A(common,A(C("Positive",rho),C("allDensityErrorsLe",c,a,t,k,l,b))),
                L(C("completeDistance",c,a,t,k,chi,l,psi,rho),Seq(Open,kap,Plus,b,Slash,D(2),Close,C("norm",rho))),quantum),
            "complete_operational_bound" => Q("c a T","k chi l psi",common,
                L(op,Seq(kap,Plus,C("maxDensityError",c,a,t,k,l),Slash,D(2)))),
            "complete_operational_nonneg" => Q("c a T","k chi l psi",common,L(D(0),op)),
            "survival_le_one" => Q("c T t","k chi",A(Original(c,t,k,chi),C("inIcc",u,D(0),t)),L(C("survival",c,k,u),D(1))),
            "probability_le_one" => Q("c x","",A(C("cLessHalf",c),C("initialInterior",I("x"),c)),L(C("p",c,I("x"),i),D(1)),V("i",mode)),
            "probability_difference" => Q("c x y","",C("True"),L(C("absProbabilityDifference",c,I("x"),I("y"),i),C("absDifference",I("x"),I("y"))),V("i",mode)),
            "terminal_error_bound" => Q("c a T B delta","k chi l psi",A(common,A(C("terminalSurvivalErrorLe",c,t,k,l,budget),C("terminalHeightErrorLe",t,k,l,delta))),
                L(kap,Seq(C("maxRootMassError",c,a,budget,delta),Plus,C("terminalPhaseError",c,t,k,chi,l,psi)))),
            _ => throw new InvalidOperationException(name)
        };
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
