using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class CommutingFidelityMomentsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/CommutingFidelityMoments.";
    private static Formula V(string s) => F.Id(s);
    private static Formula Tr(Formula x) => Call("tr", x);
    private static Formula Re(Formula x) => Call("Re", x);
    private static Formula Trace(Formula x) => Re(Tr(x));
    private static Formula Pow(Formula x, Formula j) => new Formula.Power(x, j);
    private static Formula Root(Formula x) => Call("sqrt", x);
    private static Formula Fr(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Product(params Formula[] args) => Seq(args);
    private static Formula AllMatrices(Formula body) => Seq(
        Forall, Sp, V("n"), Sp, InMacro, Sp, Call("Type"), Comma, Esc,
        OpenBracket, Call("Fintype", V("n")), CloseBracket, Esc,
        OpenBracket, Call("DecidableEq", V("n")), CloseBracket, Comma, Quad,
        Forall, Sp, V("A"), Comma, V("B"), Sp, InMacro, Sp,
        Call("Matrix", V("n"), V("n"), Seq(Mathbb, Grp(V("C")))), Comma, Quad, body);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual commuting PSD matrix resolvent moments dominate independently normalized squared Uhlmann fidelity at every positive integer order.",
        H("Commuting matrix fidelity moments"), Blocks(
            Item("response", "matrix-shifted-response", "Actual shifted matrix response",
                "For every finite index type n, every complex n by n matrix A, and every real s, response(A,s)=A(sI+A)⁻¹. The inverse is the actual matrix nonsingular inverse. At s>0 and A positive semidefinite, the shifted matrix is positive definite and the response is positive semidefinite.", true),
            Item("sandwich", "matrix-response-sandwich", "Positive square-root sandwich",
                "For every finite index type n, complex n by n matrices A,B, and real s, sandwich(A,B,s)=sqrt(response(A,s)) response(B,s) sqrt(response(A,s)). The square roots are the canonical positive square roots from continuous functional calculus. These are actual matrix operations rather than supplied eigenvalue data.", true),
            Item("gamma", "matrix-integrated-response-moment", "Integrated trace moment",
                "For every finite index type n, complex n by n matrices A,B, and natural j, gamma(j,A,B)=(1/j)∫_(s>0) Re tr(sandwich(A,B,s)^j) ds. For nonzero commuting positive semidefinite A,B and j≥1, integrability is derived by a common unitary spectral reduction and the zero-safe scalar resolvent integrability theorem.", true),
            Item("squaredNormalizedFidelity", "matrix-squared-normalized-uhlmann-fidelity", "Squared normalized Uhlmann fidelity",
                "For all finite complex square matrices A,B, put α=Re tr(A) and β=Re tr(B). squaredNormalizedFidelity(A,B)=[Re tr sqrt(sqrt(α⁻¹A)(β⁻¹B)sqrt(α⁻¹A))]². For nonzero positive semidefinite inputs, α and β are strictly positive, so these are their independently normalized trace-one states. The definition reuses CommutingMidpoint.rootFidelity and squares it; it is not the unsquared root-fidelity convention.", true),
            Item("integrable_moment", "matrix-resolvent-moment-integrability", "Derived matrix integrability",
                "For every finite index type n, all commuting positive semidefinite complex matrices A,B, and every natural j≥1, s↦Re tr(sandwich(A,B,s)^j) is integrable on s>0. Zero matrices and zero eigenvalues are allowed. Simultaneous diagonalization identifies the integrand with a finite sum of the integrable scalar resolvent moments; no integrability assumption is imposed.", false),
            Describe.Lean(DescribeId.Create("complete-commuting-fidelity-moment"),
                DeclarationHandle.Create(Prefix + "commuting_fidelity_moment"),
                H("Every finite dimension and every positive integer order"),
                StatementSource.FromAuthor(Disp(AllMatrices(Seq(
                    Forall, Sp, V("j"), Sp, InMacro, Sp, Mathbb, Grp(V("N")), Comma, Quad,
                    Call("PSD", V("A")), Sp, Land, Sp, Call("PSD", V("B")), Sp, Land, Sp,
                    V("A"), Neq, Sp, D(0), Sp, Land, Sp, V("B"), Neq, Sp, D(0), Sp, Land, Sp,
                    Product(V("A"), V("B")), Eq, Product(V("B"), V("A")), Sp, Land, Sp,
                    V("j"), Ge, D(1), Sp, Rightarrow, Sp,
                    Product(Call("M", V("j"), Trace(V("A")), Trace(V("B"))),
                        Pow(Call("F", V("A"), V("B")), V("j"))),
                    Le, Call("Gamma", V("j"), V("A"), V("B")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let n be any finite type. For all nonzero commuting positive semidefinite complex matrices A,B indexed by n, and all natural j≥1, gamma(j,A,B)≥M(j,Re tr A,Re tr B) squaredNormalizedFidelity(A,B)^j. M is FixedSumResolventKernel.scalarMoment. The theorem includes unequal positive traces, arbitrary unequal spectra, one-sided zero eigenvalues, and disjoint supports. It asserts no noncommuting extension.")),
                    Paragraph(Text("The common eigenbasis is derived, not assumed: A+iB is normal because A and B are Hermitian and commute. The existing normal-matrix spectral theorem gives a unitary diagonalization; taking the Hermitian real and imaginary parts recovers simultaneous real nonnegative spectra a_i,b_i. Star-algebra covariance of the matrix inverse and positive square root reduces the actual sandwich to diagonal entries a_i b_i/((s+a_i)(s+b_i)). Finite integral linearity gives gamma=Σ_i M(j,a_i,b_i).")),
                    Paragraph(Text("In the same basis the actual normalized Uhlmann root fidelity is Σ_i sqrt(a_i b_i)/sqrt(αβ), so its square is T²/(αβ). The scalar weighted Jensen and denominator theorem completes the matrix inequality. The argument obtains all spectral identities, positivity and integrability internally. The scalar convexity and weighted Jensen route is the supplied coordinator derivation. No literature novelty or public open-problem claim is made."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Item(string name, string id, string heading, string explanation,
        bool definition = false) => Describe.Lean(DescribeId.Create(id),
        DeclarationHandle.Create(Prefix + name), H(heading), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(explanation))),
        definition ? DescribeRole.Definition : DescribeRole.Theorem);
}
