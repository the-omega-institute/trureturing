using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class DerivativeLayerNativeGramianDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Invertible physical scaling and native Gramian limit", H("Invertible physical scaling and native Gramian limit"), Blocks(
            Describe.Lean(DescribeId.Create("derivative-layer-native-gramian"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/DerivativeLayerNativeGramian.derivative_layer_native_gramian"),
                H("Invertible physical scaling and native Gramian limit"), StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Let V be an arbitrary finite-dimensional real inner-product space, and W an arbitrary complete real inner-product space. Let B:V→V and C:V→W be arbitrary linear maps. Neither observability of the whole V nor a positive dimension is assumed.")),
                    Paragraph(Text("Put n=dim V, N(j)=the intersection of ker(C B^k) for 0≤k<j, U=N(n) orthogonal complement, E(j)=N(j) intersect N(j+1) orthogonal complement for 0≤j<n. Pi(j):V→V is the actual orthogonal projection onto E(j). All n layer indices are retained, even when their layer is zero. Write b and c for the continuous linear maps associated to B and C; i:U→V is the inclusion. All norms are induced Hilbert operator norms.")),
                    Paragraph(Text("On U let Q(j) be Pi(j) restricted to U, with its range returned to U by the orthogonal projection onto U. Put d(T)=sum sqrt(T) T^j Q(j) and e(T)=sum (sqrt(T) T^j)^(-1) Q(j). Define A(t)=c exp(t b) i and G(T)=the interval integral from zero to T of A(t) adjoint composed with A(t).")),
                    Paragraph(Text("Put P(s)=sum over j<n of s^j/j! c b^j Pi(j) i and H=the interval integral from zero to one of P(s) adjoint composed with P(s). Write Z(T,s)=sqrt(T) A(T s) e(T). Composition is written by juxtaposition in the display, and a star denotes the Hilbert adjoint.")),
                    Paragraph(Text("For every T>0, d(T)e(T) and e(T)d(T) both equal the identity on U, and e(T)G(T)e(T) equals the integral of Z(T,s) adjoint composed with Z(T,s). H has positive quadratic form at every nonzero state. There is R≥0 for which the linear error holds whenever 0<T≤1 and T times the norm of b is less than one.")),
                    Paragraph(Text("Projection orthogonality gives the inverse equations without a rank premise. The physical change of variables t=T s and self-adjointness of the scaling give the integral identity. Uniform normalized-trajectory convergence controls the difference of the two squared operators and its integral.")),
                    Paragraph(Text("For the observable Euclidean application, fix arbitrary d,p≥1 and matrices B∈R^(d×d), C∈R^(p×d) with (C,B) observable, and use their associated linear maps on V=R^d and W=R^p. The derivative filtration in "), Ref("D5/S3/Observer/Linear/DerivativeLayerNormalizedObservation.derivative_layer_normalized_observation"), Text(" has N(d)=0, so U is the whole state space. Let m be the least j with N(j+1)=0; then 0≤m<d. For j>m, N(j)=0 and E(j)=0. Thus the supplier sums over j<d reduce exactly to j=0,...,m, retaining every layer in that range and the actual exponential trajectory.")),
                    Paragraph(Text("The finite orthogonal decomposition R^d=the orthogonal sum of E(j), 0≤j≤m, supplies a subordinate orthonormal basis e_i. The upstream subordinateOrthonormalBasis and subordinateOrthonormalBasisIndex construction, followed by reindexing with Tuple.sort, orders the layer labels w_i increasingly. Each e_i belongs to E(w_i), and #{i:w_i=j}=d_j=dim E(j) for every 0≤j≤m, including zero-dimensional groups. Fix any such ordered subordinate basis for all subsequent identities and estimates; no choice of minimal layers or subordinate basis imposes an additional hypothesis on B or C.")),
                    Paragraph(Text("Let S have columns e_i in standard coordinates. The operator G(T) above has standard matrix G_standard(T)=the integral from zero to T of exp(t Bᵀ) Cᵀ C exp(t B), and matrix G_L(T)=Sᵀ G_standard(T) S in this basis. For x=sum x_j with x_j∈E(j), P(s)x=sum s^j C B^j x_j/j!, with j=0,...,m. If P_L(s) has columns P(s)e_i, put M_L=the integral from zero to one of P_L(s)ᵀ P_L(s). Thus M_L is the matrix of the constant limit operator H above in the same basis. Since S is orthogonal, these coordinate changes preserve the Euclidean operator norm and the spectrum, and det G_L(T)=det G_standard(T) because det(S)^2=1.")),
                    Paragraph(Text("For T>0 the physical scaling D_T=d(T) acts on E(j) by sqrt(T) T^j=T^(j+1/2). Its matrix is D(T)=diag(sqrt(T) T^(w_i)), and e(T) is its two-sided inverse. Write H(T)=D(T)^(-1) G_L(T) D(T)^(-1) for the normalized matrix family, distinguishing it from the constant operator H above. The exact identity is G_L(T)=D(T) H(T) D(T). All short-time estimates fix B,C, the Euclidean norms, the time unit and the chosen basis, and take T down to zero through positive values.")),
                    Paragraph(Text("For x_j∈E(j), C B^k x_j=0 when k<j. The exact factorial Taylor estimate in "), Ref("D5/S3/Observer/Linear/ExactTaylorObservationRemainder.norm_observation_taylor_remainder"), Text(" gives, for some fixed K₀≥0 and δ>0, the operator norm bound ‖sqrt(T) C exp(Ts B) D_T^(-1)-P(s)‖≤K₀ T simultaneously for every 0<T<δ and s∈[0,1]. Integrating the difference of the squared operators gives ‖H(T)-M_L‖≤K T for fixed K≥0 after shrinking δ. The supplier conditions T≤1 and T‖B‖<1 are ensured, for example, by also taking δ≤min(1,1/(1+‖B‖)). Hence H(T) tends to this same M_L along nhdsWithin(0,Ioi(0)), in the induced Euclidean operator norm.")),
                    Paragraph(Text("Positivity of the same M_L follows from "), Ref("D5/S3/Observer/Linear/DerivativeLayerGramianPositivity.derivative_layer_gramian_pos"), Text(": zero polynomial energy makes every coefficient C B^j x_j vanish; then x_j belongs both to N(j+1) and its orthogonal complement, so each x_j=0. Separately, for every T>0, "), Ref("D5/S3/Observer/Linear/ObservableTrajectoryCoordinates.observable_trajectory_coordinates"), Text(" identifies the actual physical Gramian with F*F for the injective trajectory map F:x↦(t↦C exp(t B)x) in L²(0,T). Thus G(T), G_standard(T) and G_L(T) are positive definite for every positive T, providing positivity of the same congruence used below.")),
                    Paragraph(Text("Choose a fixed μ>0 with xᵀ M_L x≥μ‖x‖². For sufficiently small positive T the norm error is at most μ/2, so a I≼H(T)≼b I with fixed a=μ/2>0 and b=‖M_L‖+μ/2>0. Congruence by the same D(T) gives a D(T)^2≼G_L(T)≼b D(T)^2. Equivalently, for every state x, a‖D_T x‖²≤⟨x,G(T)x⟩≤b‖D_T x‖². Taking a common smaller positive radius preserves all these bounds. The right-sided convergence, positive M_L, increasing w_i and positive actual congruence are exactly the inputs of "), Ref("D5/S3/Observer/Linear/GradedCongruenceSpectrum.graded_congruence_spectrum"), Text("; its application below gives every sorted spectral index and every layer group.")),
                    Paragraph(Text("The same multiplicities give q=sum_i(2w_i+1)=sum over j=0,...,m of (2j+1)d_j. For every T>0, det(D(T)^2)=the product of T^(2w_i+1)=T^q, and the exact congruence yields det G_standard(T)=det G_L(T)=T^q det H(T). Determinant is a C¹ polynomial on this fixed finite matrix space, hence locally Lipschitz at this same M_L. Combining that local bound with ‖H(T)-M_L‖≤K T gives fixed K_det≥0 and δ_det>0 with |det H(T)-det M_L|≤K_det T for 0<T<δ_det.")),
                    Paragraph(Text("In particular |det G_standard(T)/T^q-det M_L|≤K_det T. With r(T)=det H(T)-det M_L, the same actual Gramian satisfies det G_standard(T)=T^q(det M_L+r(T)), |r(T)|≤K_det T, so det G_standard(T)=T^q(det M_L+O(T)). The leading coefficient is the positive determinant of the literal integral of P_L(s)ᵀ P_L(s) in the fixed subordinate orthonormal basis. Orthogonal invariance also identifies it with the determinant of the polynomial-limit operator in standard coordinates.")),
                    Paragraph(Text("The finite derivative filtration supplies orthogonal geometry, while the exponential power series and Bochner integral supply the analytic operations."))), DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula t = F.Id("T"), s = F.Id("s"), x = F.Id("x"), r = F.Id("R");
        Formula dt = App(F.Id("d"), t), et = App(F.Id("e"), t), gt = App(F.Id("G"), t);
        Formula h = F.Id("H"), z = App(F.Id("Z"), t, s);
        return Disp(Seq(Open, Forall, Sp, D(0), Lt, t, Comma, Sp,
            dt, et, Eq, F.Id("I"), Underscore, Grp(F.Id("U")), Sp, Land, Sp, et, dt, Eq, F.Id("I"), Underscore, Grp(F.Id("U")), Sp, Land, Sp,
            et, gt, et, Eq, Int, Underscore, Grp(D(0)), Caret, Grp(D(1)), Sp,
            z, Caret, Grp(Star), z, Sp, F.Id("d"), s, Close,
            RowBreak, Grp(), Land, Sp, Open, Forall, Sp, x, InMacro, Sp, F.Id("U"), Comma,
            x, Neq, Sp, D(0), Rightarrow, Sp, D(0), Lt, Langle, Sp, x, Comma, App(h,x), Rangle, Close,
            RowBreak, Grp(), Land, Sp, Open, Exists, Sp, r, Ge, Sp, D(0), Comma, Sp,
            Forall, Sp, t, Comma, Sp, Open, D(0), Lt, t, Le, Sp, D(1), Sp, Land, Sp,
            t, new Formula.Norm(F.Id("b")), Lt, D(1), Close, Sp, Rightarrow, Sp,
            new Formula.Norm(Seq(et,gt,et,Minus,h)), Le, Sp, r,t, Close));
    }

    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
}
