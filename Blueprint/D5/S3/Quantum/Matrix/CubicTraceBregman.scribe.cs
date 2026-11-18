using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class CubicTraceBregmanDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/CubicTraceBregman";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cubic trace Bregman geometry controls both kernel deviations and stable quadratic components.",
        H("Cubic trace coercivity at singular references"),
        Blocks(
            Entry("cubic_trace_bregman_ge_weighted_square_add_abs_cube", "Global PSD coercivity",
                "Let n be any finite index type and let A,T be complex n by n positive "
                + "semidefinite matrices. Put H=A-T and let delta_i be the real eigenvalues "
                + "of the Hermitian matrix H, counted with multiplicity. With unnormalized trace, "
                + "define D3(A,T)=Re Tr(A^3)-3 Re Tr(T^2 A)+2 Re Tr(T^3). Then "
                + "Re Tr(T H^2)+sum_i |delta_i|^3 <= D3(A,T). Neither commutation, "
                + "positive definiteness nor inclusion of supports is assumed. Empty index types, "
                + "singular endpoints and repeated eigenvalues are included. "
                + "The original cubic trace expansion gives D3=3 Re Tr(T H^2)+Re Tr(H^3). "
                + "Diagonalize H alone by a unitary U and set tau_i=Re(U* T U)_{ii}. "
                + "The two PSD endpoints imply tau_i>=0 and tau_i+delta_i>=0. Consequently "
                + "delta_i^2(delta_i+2 tau_i)>=|delta_i|^3, separately for positive and "
                + "negative delta_i. Summing in this common basis and using trace cyclicity "
                + "proves the simultaneous weighted-square and absolute-cube estimate."),
            Entry("two_level_cubic_bregman_controls_components", "A two-level component bound",
                "For every finite n, real a,b>=0 and arbitrary real q, let E be a complex "
                + "Unit by n matrix and D an arbitrary complex n by n matrix. On Unit+n put "
                + "T=diag(a,bI) and X=[[a+q,E],[E*,bI+D]]. Suppose only that X is positive "
                + "semidefinite; in particular D is then Hermitian. Set "
                + "W=a q^2+b Re Tr(D*D)+(a+b) Re Tr(EE*). Then "
                + "max(W+|q|^3,2W)<=D3(X,T). The excited index n may be empty, "
                + "either spectral level may be zero, and q need not be nonnegative. "
                + "Block multiplication identifies W=Re Tr(T(X-T)^2). In the eigenbasis "
                + "of X-T, the distinguished diagonal entry q is a convex combination "
                + "of its eigenvalues with weights |U_{0i}|^2. Parseval makes the weights "
                + "sum to one. The triangle inequality and cubic Jensen give "
                + "|q|^3<=sum_i |delta_i|^3; the global coercivity theorem gives the "
                + "first bound. The original weighted-square positivity applied to X "
                + "and X-T gives 0<=Re Tr(X(X-T)^2)=W+Re Tr((X-T)^3), "
                + "which proves the second bound."),
            Paragraph(Text("The functional D3 is the Bregman remainder of the cubic trace "
                + "on the PSD cone. Convex trace theory and Klein-type nonnegativity are "
                + "established background; the estimates here are derived directly from "
                + "the spectral theorem and endpoint positivity. No assertion of literature "
                + "novelty is made. The cubic term retains control on the kernel of T, "
                + "where a uniform positive quadratic modulus cannot hold: a positive "
                + "increment epsilon along a kernel projection has cubic remainder "
                + "epsilon^3 times its rank. Positive reference levels instead weight "
                + "quadratic deviations.")),
            Paragraph(Text("For u>=0 and the full PSD Gibbs-centered matrix A=Yhat=Omega+H with "
                + "Omega=diag(u^2,u,u,1) and Re Tr(Omega^2 H)=0, the scalar "
                + "3 Re Tr(Omega H^2)+Re Tr(H^3) is exactly D3(A,Omega). "
                + "For an excited PSD matrix F, take n=Fin 2, a=u=s^4, b=1, "
                + "q=F00-u, E=F_{0,odd} and D=F_{odd,odd}-I. The two-level theorem "
                + "then controls |F00-u|^3 and the actual adjoint-square traces of the "
                + "odd block and coherence. A separate upper bound D3(F,diag(u,1,1)) "
                + "is needed to deduce any scale in s. The same coercivity can be used "
                + "in cubic conditional-expectation dynamics once an appropriate "
                + "dissipation identity is available. These applications do not supply "
                + "that identity, a map-dependent upper bound or hypercontractivity. "
                + "A corrected matrix obtained by subtracting a coherence term can be "
                + "indefinite; the PSD hypotheses must be verified before either estimate "
                + "can be applied.")))));

    private static DocumentBlock Entry(string name, string title, string text) =>
        Describe.Lean(DescribeId.Create("cubic-trace-bregman-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
