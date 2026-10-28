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
            Paragraph(Text("For a common positive trace-class rho on Blocks(Fin5,H), terminalOutput is the actual terminalKraus rho terminalKraus-adjoint. phasedJump_i is the literal absorbing jump composed with the transported character diagonal. phasedFailure is its actual trace-class congruence, taking values in Blocks(Fin6,H), with absorbing coordinate f=5. completeDistance is one half the terminal output difference norm plus the sum, over all five modes, of the time integral of the norm of the density difference. The norm is taken before integrating time. Thus arbitrary Borel time events and the unchanged reference are retained.")),
            Entry("height-control", "height_control", "The height retains original admissibility",
                C("OriginalControl", C("B"), C("T"), C("k"), D(0)),
                "For any original (k,chi), replacing chi by the constant zero function gives an original control on the same base and horizon. Absolute continuity of k follows from either original regularity alternative. This permits direct use of the existing native mode balance theorem without changing k or its clock."),
            Entry("phased-failure", "phased_failure_actual", "The failure congruence is phase independent",
                Seq(C("liveFailure"), Eq, C("phasedJump"), C("rho"), C("phasedJumpAdjoint")),
                "For every real c,a,t, every k,chi, every original mode i and every positive trace-class rho on the same Blocks(Fin5,H), liveFailure_i(t) equals phasedJump_i(t) rho phasedJump_i(t)-adjoint. The jump row has one nonzero coordinate, so composing with the diagonal multiplies it by z_i(t). The character has modulus one and cancels inside the congruence. The terminal phase remains in terminalOutput."),
            Entry("failure-events", "native_failure_bochner", "Every Borel failure event is a Bochner integral",
                C("IntegrableOn", C("phasedFailure"), C("IocIntersectionE")),
                "For every c<1/2, 0<a<c, original (k,chi), positive trace-class rho, mode i and Borel set E of real times, phasedFailure_i is Bochner integrable on (0,T] intersect E. Native mode balance supplies scalar integrability; multiplication by the fixed reference compression and its absorbing embedding supplies trace-norm integrability. No finite time partition is introduced."),
            Entry("mode-contraction", "native_mass_le", "Each surviving mode is a contraction",
                Seq(C("S", C("t")), C("p", C("k", C("t")), C("i")), Leq, C("p", C("a"), C("i"))),
                "For every t in [0,T] and i in Fin5, native mode balance and nonnegativity of the integrated squared jump amplitude give S_k(t)p_i(k(t))<=p_i(a). Consequently every successful diagonal entry has modulus at most one. The assertion uses the common initial height; survival<=1 alone would not establish this contraction."),
            Entry("joint-bound", "complete_output_bound", "The complete distance for any common positive joint input",
                Seq(C("D", C("rho")), Leq, Open, C("kappa"), Plus, C("b"), Slash, D(2), Close, C("normRho")),
                "For every arbitrary H and positive trace-class rho, and every real b with densityError_i<=b for all i, completeDistance<= (krausError+b/2) norm(rho). Here lossDensity_i=modeCoefficient_i p_i(a), densityError_i=integral_0^T |lossDensity_i(k)-lossDensity_i(l)|/p_i(a), and krausError is the operator norm of the difference of the actual terminal Kraus maps on the original five-dimensional system. The result is unnormalized and retains entangled inputs."),
            Entry("operational-bound", "complete_operational_bound", "The operational estimate IS.27",
                Seq(C("dOp"), Leq, C("kappa"), Plus, C("maxDensityError"), Slash, D(2)),
                "completeOperationalDistance is the supremum of completeDistance over all complete complex Hilbert references in any fixed universe and all positive joint trace-class inputs of trace norm one. The joint-input estimate gives d_op<=kappa+(max_i densityError_i)/2, with exactly the coefficient one on kappa. A one-dimensional reference embedded in a live coordinate proves the set of inputs is nonempty."),
            Entry("operational-positive", "complete_operational_nonneg", "The operational distance is nonnegative",
                Seq(D(0), Leq, C("dOp")),
                "Under the same common initial-height and original-control hypotheses, the operational supremum is bounded above and contains the distance of a normalized live input. Each norm integral is nonnegative, so d_op>=0. This supplies the lower bound for convergence by squeezing."),
            Entry("survival-unit", "survival_le_one", "Survival never exceeds one",
                Seq(C("S", C("t")), Leq, D(1)),
                "For every original (k,chi) and every t in [0,T], S_k(t)<=1. Native bounds put the height strictly between zero and c, so each term in its hazard is nonnegative."),
            Entry("probability-unit", "probability_le_one", "Every original probability is at most one",
                Seq(C("p", C("x"), C("i")), Leq, D(1)),
                "For c<1/2, 0<x<c and every mode i, positivity and the original probability sum give p_i(x)<=1."),
            Entry("probability-difference", "probability_difference", "Every probability coordinate is nonexpansive",
                Seq(C("absProbabilityDifference"), Leq, C("absHeightDifference")),
                "For arbitrary real c,x,y and all five original modes, |p_i(x)-p_i(y)|<=|x-y|. Their slopes are 1,-1,0,-1,1, including the constant mode 2 and mode 13 at index four."),
            Entry("terminal-bound", "terminal_error_bound", "The terminal amplitude and character estimate IS.29",
                Seq(C("kappa"), Leq, C("maxRootMassError"), Plus, C("phaseError")),
                "In addition to the common control hypotheses, suppose |S_k(T)-S_l(T)|<=B and |k(T)-l(T)|<=delta. Then kappa<=max_i sqrt((B+delta)/p_i(a))+max_i |z_i(T)-w_i(T)|. The terminal phase error is an independent certificate. The amplitude difference uses |S_k p_i(k)-S_l p_i(l)|<=B+delta and the square-root inequality |sqrt(x)-sqrt(y)|<=sqrt(|x-y|). Contractivity bounds the coefficient of the character difference by one."),
            Paragraph(Text("The terminal proof writes A rho A-adjoint minus B rho B-adjoint as (A-B) rho A-adjoint plus B rho (A-B)-adjoint. The general trace-class ideal estimate bounds both mixed products, including nonpositive products, by their operator norms times norm(rho). The diagonal amplification bound holds on arbitrary H. The failure contribution is exactly sum_i densityError_i norm(rho_ii), where rho_ii is the compression of that same rho. Positivity is used only for these diagonal blocks and their trace partition sum_i norm(rho_ii)=norm(rho).")),
            Paragraph(Text("Terminal characters are not recovered from height data. No relative phase waveform, phase unwrapping, acquisition service, restart permission, physical realization or full programme reconstruction follows from these estimates.")))));

    private static DocumentBlock Entry(string id, string declaration, string title, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Quantum/Fibers/OriginalCompleteOutputStability." + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

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
