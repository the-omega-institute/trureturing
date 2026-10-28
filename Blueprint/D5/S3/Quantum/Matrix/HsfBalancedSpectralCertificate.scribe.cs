using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class HsfBalancedSpectralCertificateDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite weighted Gram certificate proves the noncommutative two-level balanced cubic supplier.",
        H("Two spectral levels with arbitrary complex matrix blocks"),
        Blocks(
            Entry("den", "Spectral denominator",
                "Set q(r)=r²+r+1; this is positive for every r>0.", DescribeRole.Definition),
            Entry("aux", "Auxiliary positive polynomial",
                "Set a(r)=4r²+7r+4. It enters the finite Gram factorization.", DescribeRole.Definition),
            Entry("tau", "First divided-difference overlap",
                "For the normalized spectral values 1,r³, tau(r)=3 sqrt(r)(r+1)/(2q(r)). The first coefficient is (2/3) times the Schur transform with this off-diagonal multiplier.", DescribeRole.Definition),
            Entry("kappa", "Repeated-index remainder",
                "The exact rational remainder is r(r-1)²(r²-r+1)(r²+7r+1)/(12q(r)^4). The proof derives it from the finite coefficient kernels and uses its nonnegativity, including r=1.", DescribeRole.Definition),
            Entry("gap", "Second Gram weight",
                "The weight d=(r-1)²(4r²+7r+4)/(4q²) equals 1-tau² and is nonnegative.", DescribeRole.Definition),
            Entry("gramGap", "Remaining Gram weights",
                "Both remaining weights equal rho=r(r-1)²(r+1)²(5r^4+22r³+36r²+22r+5)/(3q^4(4r²+7r+4)). All weights are nonnegative, without a spectral-gap denominator.", DescribeRole.Definition),
            Entry("pv", "First coordinate of p",
                "This rational square-root coefficient is the v-coordinate of the finite Gram vector p.", DescribeRole.Definition),
            Entry("qv", "First coordinate of q",
                "This rational coefficient is the v-coordinate of the finite Gram vector q and the coefficient of CC* in the upper diagonal block of B.", DescribeRole.Definition),
            Entry("pw", "Overlap of p with w",
                "The exact coefficient pw equals tau times pv plus d times pc. It is also the coefficient of C*C in the lower diagonal block of B.", DescribeRole.Definition),
            Entry("qw", "Overlap of q with w",
                "The exact coefficient qw equals tau times qv plus d times qc.", DescribeRole.Definition),
            Entry("pc", "Second coordinate of p",
                "The coefficient pc=(3r³+15r²+19r+8)/(q(4r²+7r+4)) has no division by r-1.", DescribeRole.Definition),
            Entry("qc", "Second coordinate of q",
                "The coefficient qc=-sqrt(r)(r-1)(2r²+3r+2)/(q(4r²+7r+4)) also includes r=1 directly.", DescribeRole.Definition),
            Entry("pn", "Squared length of p",
                "The rational coefficient pn is proved equal to pv²+d pc²+rho. It is independently constrained by 4-tau²-2qv-pn=kappa.", DescribeRole.Definition),
            Entry("qn", "Squared length of q",
                "The rational coefficient qn is proved equal to qv²+d qc²+rho and satisfies 4-tau²-2pw-qn=kappa.", DescribeRole.Definition),
            Entry("tr", "Real matrix trace",
                "Use Re Tr on arbitrary finite square complex matrices. Rectangular cyclic trace identities never commute the matrix factors.", DescribeRole.Definition),
            Entry("direction", "Normalized block direction",
                "For arbitrary finite index types m,n, let S=[[A,C],[C*,H]], where C is an m-by-n complex matrix. Positivity is imposed on this full block matrix.", DescribeRole.Definition),
            Entry("first", "First balanced coefficient",
                "L1=(2/3)[[A,tau C],[tau C*,H]]. The proof identifies it with P^-1(P R+R P)P^-1 for the cube-root coefficient R.", DescribeRole.Definition),
            Entry("second", "Second balanced coefficient",
                "The upper diagonal block is -A²/9-r³(2r+1)CC*/(3q²), the lower diagonal block is -H²/9-(r+2)C*C/(3q²), and the upper off-diagonal block is -sqrt(r)((2r+1)AC+r²(r+2)CH)/(3q²). The lower block retains the reversed ordered products.", DescribeRole.Definition),
            Entry("gramRow", "Noncommutative Gram row",
                "The row X(v,p,q,w) is [[v A,p C],[q C*,w H]], with four real coefficients and the original ordered matrix products.", DescribeRole.Definition),
            Entry("gramDiag", "Diagonal Gram row",
                "V(v,w)=diag(v I,w I) on the direct sum of the two index types.", DescribeRole.Definition),
            Entry("transport", "The first Schur transform",
                "T=[[A,tau C],[tau C*,H]]=(3/2)L1. No invertibility of T is assumed or used.", DescribeRole.Definition),
            Entry("balancedQuadratic", "Actual quadratic kernel",
                "B=-3L2+(3/2)L1². Direct block multiplication identifies it with the symmetrized finite cross moment.", DescribeRole.Definition),
            Entry("squareEnergy", "Finite weighted square",
                "The four rows use v=(1,0,0,0), w=(tau,1,0,0), p=(pv,pc,1,0), q=(qv,qc,0,1), with weights (1,d,rho,rho). The energy is the weighted sum of Re Tr((X_j-2V_j W)* S (X_j-2V_j W)), where * means adjoint. The last two V_j vanish. PSD S makes every summand nonnegative, including singular S.", DescribeRole.Definition),
            Entry("baseRoot", "Normalized spectral root",
                "P=diag(I,r I), so Y=P³ has spectral values 1,r³ with arbitrary multiplicities.", DescribeRole.Definition),
            Entry("inverseRoot", "Explicit balancing root",
                "D=diag(I,r^-1 I)=P^-1 for r>0.", DescribeRole.Definition),
            Entry("solveRoot", "Cubic coefficient solver",
                "The inverse of E ↦ P²E+PEP+EP² divides the diagonal blocks by 3 and 3r² and the off-diagonal blocks by q. These denominators are nonzero for r>0, including repeated levels.", DescribeRole.Definition),
            Entry("rootFirst", "First cube-root coefficient",
                "R has diagonal blocks A/3,rH/3 and off-diagonal blocks r sqrt(r) C/q and its adjoint. Its linear cubic coefficient is exactly K=baseDirection.", DescribeRole.Definition),
            Entry("rootSecond", "Second cube-root coefficient",
                "Q is obtained by solving P²Q+PQP+QP²+PR²+RPR+R²P=0. Its displayed finite block kernels are checked against this equation and against L2.", DescribeRole.Definition),
            Entry("rootThird", "Third cube-root coefficient",
                "U is defined by applying solveRoot to the negative ordered cubic cross terms P(RQ+QR)+RPQ+QPR+(RQ+QR)P+R³. This defines the coefficient before deriving its trace normalization.", DescribeRole.Definition),
            Entry("third", "Third balanced coefficient",
                "L3=D(PU+UP+RQ+QR)D, formed by squaring the cube-root series. The proof independently derives Tr L3=Tr(L1 L2)-(1/3)Tr L1³+(2/9)Tr S³ from these actual coefficient formulas.", DescribeRole.Definition),
            Entry("pairEnergy", "Positive repeated-index cyclic words",
                "E=Re Tr(ACC*)+Re Tr(HC*C). Principal-block positivity and PSD congruence prove E>=0; no rank assumption is made.", DescribeRole.Definition),
            Entry("supplier", "The cubic supplier",
                "F(Z)=Re Tr L3+2 Re Tr(Z L2)+Re Tr(L1 Z²)-(5/48)Re Tr L1³. The matrix coefficients come from the cube-root recurrence, independently of the certificate.", DescribeRole.Definition),
            Entry("cubeLinear", "Linear cube coefficient",
                "For P=diag(I,rI), define A_P(R)=P²R+PRP+RP². The block denominators prove that this map is injective.", DescribeRole.Definition),
            Entry("cubeQuadratic", "Quadratic cube cross terms",
                "The quadratic cross terms are PR²+RPR+R²P.", DescribeRole.Definition),
            Entry("cubeCubic", "Cubic cube cross terms",
                "The cubic cross terms are P(RQ+QR)+RPQ+QPR+(RQ+QR)P+R³; all orders are retained.", DescribeRole.Definition),
            Entry("baseDirection", "Physical direction in the spectral frame",
                "K=diag(I,r sqrt(r) I) S diag(I,r sqrt(r) I). Its off-diagonal blocks are r sqrt(r) C and r sqrt(r) C*, and its lower diagonal block is r³H.", DescribeRole.Definition),
            Entry("supplier_of_cubic_recurrence", "Pointwise supplier from the actual cubic recurrences",
                "For all finite index types m,n, every r>0, PSD S=[[A,C],[C*,H]], Hermitian Z, "
                + "and matrices R,Q,U satisfying A_P(R)=K, A_P(Q)+PR²+RPR+R²P=0, "
                + "A_P(U)+P(RQ+QR)+RPQ+QPR+(RQ+QR)P+R³=0, form "
                + "L1=D(PR+RP)D, L2=D(PQ+QP+R²)D and L3=D(PU+UP+RQ+QR)D. "
                + "Then 0<=kappa(r)E/6<=F(Z). The proof identifies the three arbitrary "
                + "coefficient matrices with the explicit finite spectral kernels using "
                + "injectivity of A_P. No desired inequality is an input hypothesis.", DescribeRole.Theorem),
            Paragraph(Text("The exact internal identity is 6F(Z)=kappa(r)E+squareEnergy(Z+L1/2). "
                + "It follows from the actual third-trace normalization and the independently "
                + "proved finite Gram moments. The unshifted Gram energy U_G is "
                + "Tr A³+Tr H³+(2qv+pn)Tr(ACC*)+(2pw+qn)Tr(HC*C). "
                + "Consequently 4Tr S³-Tr T³-3U_G=3kappa(r)E. The identity includes "
                + "r=1 and singular directions directly, and uses no pseudoinverse, "
                + "Sylvester minimization, Mellin-integral premise, rank restriction, "
                + "commutativity, spectral floor, or trace normalization.")),
            Paragraph(Text("The external target is He–Saunderson–Fawzi, "
                + "arXiv:2502.05627v1 Conjecture 6.2, journal DOI 10.1007/s10107-025-02314-0 "
                + "Conjecture 1; see Library/Divergence/he2025operatorconvexity.md. "
                + "Cubic-series multiplication, cyclic trace, and PSD congruence are classical. "
                + "This repository certificate is not attributed to that paper, and no "
                + "literature novelty is asserted. The theorem has an explicit algebraic "
                + "coefficient-recurrence interface. Identification with actual CFC derivatives, "
                + "unitary spectral coordinates and common-scale normalization is a separate "
                + "bridge. Triangle-free spectra with more than two levels are not formalized "
                + "here. Three-distinct-level interactions, independent X,Y, all alpha>2 and "
                + "the complete continuing HSF conjecture remain open.")),
            Paragraph(Text("The corresponding Reg mirror supplies the typed whole-telescope "
                + "arena, actual-law bridge, rejected intervention, sensitivity and observational "
                + "dependence. Source-selection reconstruction and declared-template binding are "
                + "unfinished under https://github.com/the-omega-institute/trureturing/issues/23103. "
                + "This is not a declared_validated registration or independent review.")))));

    private static DocumentBlock Entry(string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("hsf-balanced-spectral-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
