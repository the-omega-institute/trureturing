using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class HsfLocalSpectrumSupplierDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/HsfLocalSpectrumSupplier";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A quantitative local all-Z supplier for actual CFC derivatives at any finite positive diagonal spectrum.",
        H("The local finite-spectrum two-thirds supplier"),
        Blocks(
            Describe.Lean(DescribeId.Create("hsf-local-spectrum-actual-supplier"),
                DeclarationHandle.Create(Module + ".finite_spectrum_local_supplier"),
                H("The exact cross-level affine slice"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let d be arbitrary, p_i positive real numbers with at least "
                        + "two distinct levels, and P=diag(p_i) a complex matrix. Put "
                        + "tau_ij=3 sqrt(p_i p_j)(p_i+p_j)/(2(p_i squared+p_i p_j+p_j squared)). "
                        + "The definition crossGap is the minimum of 1-tau_ij squared over "
                        + "p_i unequal to p_j. It retains every multiplicity and is strictly "
                        + "positive. Let H be any complex Hermitian matrix whose ij entry "
                        + "vanishes whenever p_i=p_j. In particular every entire equal-level "
                        + "block, including the diagonal, vanishes. Let r be its explicitly "
                        + "fixed Frobenius norm, independently of the operator norm used by CFC.")),
                    Paragraph(Text("Assume r <= 3 crossGap/32, and set S=I+H. For the actual "
                        + "function F(t)=P inverse CFC.rpow(P cubed+t P^(3/2) S P^(3/2),2/3) "
                        + "P inverse, define B_j=(j factorial) inverse times iteratedDeriv j F 0. "
                        + "For every complex Hermitian Z the theorem proves crossGap>0 and "
                        + "Re Tr(B_3+2 Z B_2+B_1 Z squared-(5/48) B_1 cubed) "
                        + ">= crossGap r squared/6. Neither derivative formulas, trace identities, "
                        + "positivity of H, nor the desired inequality are hypotheses.")),
                    Paragraph(Text("The proof consumes RpowPencilTaylor's actual cube-root "
                        + "jet recurrences and normalized two-thirds jet bridge. The positive "
                        + "diagonal cubic linearization has divisor p_i squared+p_i p_j+p_j squared. "
                        + "Solving the first two ordered equations gives the first Schur "
                        + "multiplier A_ij=tau_ij H_ij and a second kernel c(a,b,c)="
                        + "sqrt(a b)c cubed(a b+c(a+b))/((a squared+a b+b squared)"
                        + "(a squared+a c+c squared)(c squared+c b+b squared)). "
                        + "The kernel lies between zero and 2/3. Entrywise modulus domination "
                        + "and Frobenius submultiplicativity bound D=-3 B_2(H)-A squared/3 "
                        + "by norm D <= 2 r squared, while norm A <= r. The cross-level "
                        + "support gives g=Tr H squared-Tr A squared >= crossGap r squared.")),
                    Paragraph(Text("HsfLocalSpectrumTrace supplies actual quadratic and cubic "
                        + "trace normalization. The ordered radial shift then identifies "
                        + "C=B_1(S)=(2/3)(I+A), B_2(S)=-(I+A) squared/9-D/3, and Tr D=g. "
                        + "For R=Z-C/4 and h=4 Tr H cubed-4 Tr A cubed-6 Tr(A D), "
                        + "cyclic trace alone gives 18 J=6g+h+12(Tr((I+A)R squared)-Tr(D R)). "
                        + "No matrix factors are commuted. Frobenius trace Cauchy-Schwarz "
                        + "bounds the real part of h below by -20 r cubed. If q=norm R, "
                        + "the last term is at least 6 q squared-24 r squared q, hence "
                        + "at least -24 r to the fourth power by the nonnegative square "
                        + "6(q-2 r squared) squared. The stated radius implies r<=1/2 and "
                        + "32r<=3 crossGap, giving 18 J>=3 crossGap r squared.")),
                    Paragraph(Text("There is no division by r, so H=0 is included. The number "
                        + "of spectral levels and the dimension are unrestricted within finite "
                        + "dimension; complex cycle phases and repeated spectral levels are "
                        + "allowed. The support condition on equal-level blocks is essential "
                        + "to this positive gap. The radius is local in H and can shrink "
                        + "when distinct levels approach one another. This theorem constructs "
                        + "no Sylvester inverse or minimizing Z and proves no global neighborhood, "
                        + "arbitrary direction supplier, or full He–Saunderson–Fawzi conjecture."))),
                DescribeRole.Theorem),
            Paragraph(Text("The proof reuses GNSMatrix's Frobenius-square trace identity, "
                + "CartesianVariance.trace_product_cauchy and Matrix.frobenius_norm_mul. "
                + "It extends the finite spectral coefficient estimates; it does not "
                + "reprove the radial or two-level certificates. The contextual source is "
                + "He–Saunderson–Fawzi, arXiv:2502.05627v1 Conjecture 6.2 / "
                + "DOI 10.1007/s10107-025-02314-0 Conjecture 1. No novelty or external "
                + "official acceptance claim is made.")),
            Paragraph(Text("The full-telescope typed Reg attempt retains the radius implication "
                + "and actual CFC readout. Source-selection reconstruction and the escape "
                + "coordinate remain unfinished under https://github.com/the-omega-institute/"
                + "trureturing/issues/23103; declared_validated is not claimed.")))));
}
