using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4;

internal sealed class FiniteGaussianCap475Document : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianCap475.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Physical comparison for finite reflected Gaussian sources",
        H("Physical comparison for finite reflected Gaussian sources"),
        Blocks(
            Paragraph(Text("For a finite index type, real coefficients c and real sites a, set F(x)=sum_i c(i)*exp(9*a(i)/2-exp(2*a(i))*x). Signed coefficients and repeated sites are allowed. The symmetry is a permutation r with c(r(i))=c(i) and a(r(i))=-a(i); this is a condition on the finite source, not an assertion that F is an arbitrary even function of x.")),
            Paragraph(Text("Write H=integral_(0,infinity) x^(7/2)*F(x)^2 dx. Let C(x)=(x/pi)^(5/2)-4*(x/pi)^(-7/2) for x>pi and C(x)=0 otherwise, and Q=integral_(0,infinity) x^(7/2)*C(x)*F(x)^2 dx. The linked Lean declarations are the proof source; this exposition makes no independent claim of final acceptance or public priority.")),
            Describe.Lean(
                DescribeId.Create("finite-gaussian-cap475-coercivity"),
                DeclarationHandle.Create(Owner + "finiteGaussian_cap475_coercivity"),
                H("Coercivity on the same mass-zero source"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every finite real source with the stated permutation symmetry and sum_i c(i)=0, the declaration states (3/4)*H<=Q. It assumes no matrix-entry enclosure, integrability, expansion, Parseval identity, nonzero head, or nonzero source as an additional premise.")),
                    Paragraph(Text("The argument joins the actual normalized Laguerre coefficients to the sixteen-even-mode matrix, uses its exact rational certificate with the proved actual entry enclosures, and retains all modes from k=16 onward. The actual central Mellin mass equation identifies the complete tail charge with minus the head charge. The full signed compact multiplier is paid with the original head cost 2/5 and remainder cost 44; the Jacobi boundary payment retains the 15/16 edge."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-gaussian-cap475-tail-quotient"),
                DeclarationHandle.Create(Owner + "finiteGaussian_cap475_ratio"),
                H("Strict tail quotient for a globally nonzero source"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("With the same symmetry and zero total mass, assume in addition that F is not identically zero on the whole real line. For D=integral_(pi,infinity) F(x)^2 dx and N=integral_(pi,infinity) x^6*F(x)^2 dx, the declaration states N/(pi^6*D)>19/4. Actual analytic nonvanishing supplies D>0 and H>pi^(7/2)*D. The exact multiplier identity is Q=pi^(-5/2)*N-4*pi^(7/2)*D.")),
                    Paragraph(Text("This displayed quotient is the concrete tail quotient in the declaration. No identification with an authoritative Suzuki M definition is supplied here. The source condition sum_i c(i)=0 has not been identified with the complete Theta+B+even-transform mean-zero constraint of actualSuzukiEvenBProfile. Applying WeilSquarePositivityCriterion.weilSquarePositivity_implies_rh still requires complete zeroSum nonnegativity for every admissible convolution-square test and a proved correspondence of domains and quadratic forms; these finite-source statements do not provide those bridges."))),
                DescribeRole.Theorem))));
}
