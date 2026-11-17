using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class QubitWeightedCommutatorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Density-weighted qubit commutators in the Hilbert-Schmidt norm.",
        H("Density-weighted qubit commutators"), Blocks(
            Describe.Lean(
                DescribeId.Create("qubit-weighted-commutator-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/QubitWeightedCommutator.qubit_weighted_commutator_bound"),
                H("The all-complex qubit estimate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For arbitrary complex two by two matrices X and W and every positive semidefinite b with unnormalized trace Tr(b)=1, the theorem proves ||XW-WX||_HS <= sqrt(2)||sqrt(b)(XW-WX)||_HS + (1+sqrt(2))||XW*-W*X||_HS. Here star is conjugate transpose, sqrt(b) is the positive continuous-functional-calculus square root, and every matrix norm in the statement is explicitly Frobenius: ||A||_HS squared is Tr(A* A). No Hermiticity or normality assumption is imposed on X or W. Scalar W and singular b are included.")),
                    Paragraph(Text("Remove the scalar trace parts and write V=W-(Tr(W)/2)I. When V is nonzero, project X0 onto the line spanned by V*: alpha=Tr(X0 V)/||V||_HS squared and D=X0-alpha V*, so Tr(DV)=0. A direct complex entry calculation for traceless A,V gives ||[A,V]||_HS squared = 2(||A||_HS squared ||V||_HS squared - |Tr(A V*)| squared). Applied to D,V and D,V*, it bounds R=[D,V] by [X,W*]. The complementary term N=alpha[V*,V] is a scalar multiple of a traceless Hermitian matrix. Its square identity and trace cyclicity give the exact equality ||N||_HS=sqrt(2)||sqrt(b)N||_HS. Frobenius submultiplicativity and ||sqrt(b)||_HS=1 then control the weighted residual. The triangle inequality yields the displayed constants. The scalar case is split before the only division; the proof uses no inverse or lower spectral bound for b.")),
                    Paragraph(Text("The norm/trace supplier is GNSMatrix.frobenius_norm_sq_eq_trace. Matrix trace cyclicity, Frobenius product and adjoint norm bounds, and the semidefinite CFC square-root identity are reused from Mathlib. The projection and residual estimate is the additional inference; the finite entry identities and scalar adaptations are internal consumed helpers. This is a finite-dimensional mathematical estimate, with no claim of literature novelty or physical realization.")),
                    Paragraph(Text("The intended consumer is the original three-qubit CMI/Sylvester repair argument. In Hermitian Hilbert-Schmidt orthonormal outer bases, write Y=sum E_a tensor X_a and Z=sum W_c tensor F_c. Coefficientwise application, Parseval and finite Euclidean Minkowski would give ||J||_HS <= sqrt(2)||(I tensor sqrt(b) tensor I)J||_HS + (1+sqrt(2))||S||_HS for J=[Zbar,Ybar] and S=[Ybar,Zbar*], without an outer dimension factor. This tensor aggregation is not Lean-realized here. The entropy-to-physical-Sylvester bridge and the full singular sixth-root CMI-to-original-ABC-Markov theorem remain unproved."))),
                DescribeRole.Theorem))));
}
