using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class HsfThreeLevelSupplierDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/HsfThreeLevelSupplier";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual three-level CFC supplier and positive-definite Sylvester rigidity.",
        H("At most three positive spectral levels"),
        Blocks(
            Describe.Lean(DescribeId.Create("hsf-three-level-supplier-target"),
                DeclarationHandle.Create(Module + ".ThreeLevelSupplierTarget"),
                H("The original actual-derivative proposition"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let n be any finite index type, level a map from n to "
                        + "Fin 3, and p three positive real labels. Put P=diag(p(level(i))). "
                        + "The map level need not be surjective, p need not be injective, "
                        + "and n may be empty. For a complex positive-semidefinite matrix S, "
                        + "define F(t)=P inverse CFC.rpow(P cubed+t times "
                        + "CFC.rpow(P,3/2) S CFC.rpow(P,3/2),2/3) P inverse. "
                        + "Define B_j=(j factorial) inverse times iteratedDeriv j F at zero.")),
                    Paragraph(Text("ThreeLevelSupplierTarget states that for every such "
                        + "choice and every complex Hermitian Z, the real trace "
                        + "J=Re Tr(B_3+2 Z B_2+B_1 Z squared-(5/48) B_1 cubed) is "
                        + "nonnegative. The coefficients are the actual factorial-normalized "
                        + "CFC derivatives. No coefficient, trace identity, spectrum floor, "
                        + "smallness condition on S, or bound on Z is a premise."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hsf-three-level-actual-supplier"),
                DeclarationHandle.Create(Module + ".actual_threeLevel_supplier"),
                H("The supplier for arbitrary finite multiplicities"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The theorem proves ThreeLevelSupplierTarget with its "
                        + "complete original quantifiers. Arbitrary complex phases, repeated "
                        + "positive labels, empty level fibers, the empty carrier and singular "
                        + "positive-semidefinite S are included. The number three bounds "
                        + "the spectral values, not the dimension of the matrix.")),
                    Paragraph(Text("For distinct labels write q(a,b)=a squared+ab+b squared "
                        + "and g(a,b)=3(a+b)/(2q(a,b)). An explicit rational LDL completion "
                        + "proves positivity of the three-by-three base Gram matrix. Its "
                        + "CFC square root realizes the base coordinates. The rational "
                        + "residual budgets satisfy an exact polynomial gap identity with "
                        + "a strictly positive coefficient polynomial. Denominator clearing "
                        + "and polynomial identities are proved in Lean. Allocating the "
                        + "signed residual cross term among three positive budgets gives "
                        + "positive two-by-two Gram determinants. Explicit real square-root "
                        + "coordinates retain both signs of each allocated cross term.")),
                    Paragraph(Text("The resulting coefficient space has three base and six "
                        + "residual coordinates. Its dimension is independent of n. All "
                        + "mixed and cyclic coefficient identities include repeated indices. "
                        + "Lift the first coefficient vectors to real diagonal matrices V_a "
                        + "and the ordered second vectors to matrices M_a. Writing "
                        + "X_ij=tau(p(level(i)),p(level(j))) S_ij and Q as below, the moments "
                        + "are sum V_a adjoint S V_a=X, sum of "
                        + "(V_a adjoint S M_a+M_a adjoint S V_a)=2 Q, and "
                        + "sum Re Tr(M_a adjoint S M_a)=(4 Re Tr(S cubed)-Re Tr(X cubed))/3. "
                        + "The proof preserves ordered products and complex triangle phases.")),
                    Paragraph(Text("For W=Z+X/3, expanding the positive weighted row squares "
                        + "sum Re Tr((M_a-2 V_a W) adjoint S (M_a-2 V_a W)) gives "
                        + "(4 Re Tr(S cubed)-Re Tr(X cubed))/3-4 Re Tr(Q W)+4 Re Tr(X W W). "
                        + "HsfLocalSpectrumSupplier.actual_shifted_supplier_identity identifies "
                        + "this expression with 6 J using the actual first and second CFC "
                        + "coefficients and cubic trace normalization. Neither M_a nor any "
                        + "pair of matrix factors is assumed to commute or be simultaneously "
                        + "diagonal. When labels coincide, an actual fiber equivalence and "
                        + "common positive scale transport the existing two-level CFC supplier; "
                        + "the singular base Gram inverse is not evaluated."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hsf-three-level-pd-sylvester-rigidity"),
                DeclarationHandle.Create(Module + ".actual_threeLevel_PD_sylvester"),
                H("The Hermitian Sylvester solution and exact equality criterion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Retain the same arbitrary finite carrier, level map, "
                        + "positive labels and P, and now assume S positive definite. Write "
                        + "a_i=p(level(i)), tau for HsfLocalSpectrumSupplier.spectralTau, "
                        + "and c for HsfLocalSpectrumSupplier.spectralKernel. Define "
                        + "X_ij=tau(a_i,a_j) S_ij and "
                        + "Q_ij=sum over k of ((2/3) tau(a_i,a_k) tau(a_k,a_j) "
                        + "+3 c(a_i,a_j,a_k)) S_ik S_kj. Put D=Q-X squared. "
                        + "These are the original ordered X, Q and D.")),
                    Paragraph(Text("The theorem proves X positive definite and constructs a "
                        + "Hermitian matrix Y satisfying the actual Sylvester equation "
                        + "X Y+Y X=D. For that Y the energy "
                        + "E=4 Re Tr(S cubed-X cubed)-6 Re Tr(X D)-6 Re Tr(D Y) "
                        + "is nonnegative, and E=0 if and only if P S=S P. There is no "
                        + "assumed Sylvester solution, jet formula, trace identity or "
                        + "commutativity hypothesis. Empty carriers and repeated labels "
                        + "remain included. The direction must be positive definite for "
                        + "this additional energy and rigidity statement.")),
                    Paragraph(Text("Strict positivity of X follows from the common kernel "
                        + "of the diagonal V_a maps being zero and the positive definiteness "
                        + "of S. A unitary eigenbasis of X solves the Sylvester equation "
                        + "entry by entry with positive denominators lambda_i+lambda_j. "
                        + "The same computation proves injectivity of the Sylvester operator "
                        + "on all matrices. An ordinary inverse of X is not substituted "
                        + "for this operator.")),
                    Paragraph(Text("For W=X/2+Y, the exact cyclic-trace computation gives "
                        + "E=3 sum Re Tr((M_a-2 V_a W) adjoint S (M_a-2 V_a W)). "
                        + "A weighted square has zero real trace precisely when its row "
                        + "matrix vanishes, since S is positive definite. The six residual "
                        + "coordinates have V_a=0; their strictly positive Gram budgets "
                        + "force every entry of S between distinct spectral levels to "
                        + "vanish when E=0. This is exactly P S=S P. Conversely, commutation "
                        + "gives X=S, Q=S squared, D=0 and Y=0, hence E=0. A faithful "
                        + "injective relabeling with unused positive slots covers all label "
                        + "collisions without changing any pulled-back spectral value."))),
                DescribeRole.Theorem),
            Paragraph(Text("These results extend the existing local and two-level actual-CFC "
                + "suppliers. They assert no supplier for more than three spectral values "
                + "and no full He–Saunderson–Fawzi conjecture or literature novelty claim.")),
            Paragraph(Text("Full-telescope typed Reg attempts accompany both new public "
                + "endpoints. Source-selection reconstruction and escape evidence remain "
                + "unfinished under https://github.com/the-omega-institute/trureturing/issues/23103. "
                + "No declared_validated registration is claimed.")))));
}
