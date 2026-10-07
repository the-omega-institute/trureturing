using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class PolynomialFockDerivativePowerOPEDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every integer mode of a derivative-labelled Fock power-state field has an explicit polynomial output.",
        H("Derivative-Labelled Polynomial Fock Coefficients"),
        Blocks(
            Paragraph(Text("The complex polynomial Fock space is C[X_0,X_1,...]. "
                + "The current modes are multiplication by X_j at mode -j-1, "
                + "zero at mode zero, and (j+1) times differentiation in X_j "
                + "at mode j+1. The actual state-field map Y is defined by "
                + "the monomial basis and right-nested normal products. "
                + "The field of X_a is the divided derivative of order a "
                + "of the current, using 1/a! times the ordinary derivative.")),
            Paragraph(Text("Independently of Y, define A(a,z) as the formal "
                + "power series with coefficient binomial(j+a,a) X_(j+a) "
                + "at every natural j. B(a,r,d) is the coefficient of z^d "
                + "in A(a,z)^r when d>=0 and is zero when d<0. Define "
                + "c(a,b)=(-1)^a (b+1) binomial(a+b+1,a). Thus B(a,0,0)=1 "
                + "and B(a,0,d)=0 for every nonzero integer d.")),
            Describe.Lean(
                DescribeId.Create("polynomial-fock-derivative-power-state-coefficients"),
                DeclarationHandle.Create(
                    "D5/S3/VertexAlgebra/PolynomialFockDerivativePowerOPE.derivative_power_state_coefficients"),
                H("The actual two-labelled field output at every integer mode"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/VertexAlgebra/matsuo1997freeboson")),
                Blocks(
                    Paragraph(Text("For every natural a,b,p,q and integer n, "
                        + "Y(X_a^p)_n applied to X_b^q equals the sum over "
                        + "0<=k<=min(p,q) of binomial(p,k) times the falling "
                        + "factorial q(q-1)...(q-k+1), times c(a,b)^k, times "
                        + "B(a,p-k,(a+b+2)k-n-1) X_b^(q-k). Scalar factors "
                        + "are complex numbers. There are no extra hypotheses "
                        + "on the labels, powers or mode sign.")),
                    Paragraph(Text("Every zeroth power, including c(a,b)^0, "
                        + "and the falling factorial at k=0 is one. When p=0 "
                        + "the output is X_b^q at mode -1 and zero elsewhere. "
                        + "When q=0 the output is B(a,p,-n-1). When a=b=0 "
                        + "the formula specializes to the unlabelled power-state "
                        + "coefficient relation.")),
                    Paragraph(Text("The divided-current mode at -j-1 creates "
                        + "binomial(j+a,a) X_(j+a). On X_b^q its nonnegative "
                        + "modes vanish except at a+b+1, where its output is "
                        + "q c(a,b) X_b^(q-1). The actual minus-one normal "
                        + "product therefore has a creation convolution and "
                        + "one annihilation contribution. A finite support "
                        + "cutoff identifies the first branch with A(a)^(r+1). "
                        + "Pascal's identity and falling factorials combine "
                        + "the branches through induction on the left power.")),
                    Paragraph(Text("The free-boson reference supplies the "
                        + "classical divided-derivative contraction and "
                        + "polynomial Fock normalization; it does not state "
                        + "this exact all-integer output formula. These are "
                        + "formal algebraic coefficients. They do not establish "
                        + "analytic convergence, module fusion, a Monster "
                        + "realization, complete boundary conformal field "
                        + "theory or spacetime dynamics."))),
                DescribeRole.Theorem))));
}
