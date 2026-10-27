using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

internal sealed class ActualSuzukiThetaExcessDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiThetaExcess.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original physical H6 condition supplies almost "
            + "everywhere convergence of the complete physical theta series, preservation "
            + "of H6 and control of the normalized sixth-moment excess for the same source.",
        H("Actual H6 Sources and the Complete Theta Transform"),
        Blocks(
            Paragraph(Text(
                "The same original H6 estimates also support the classical Mobius inverse "
                    + "on this actual physical space. Put T(F)=fullTheta(F), "
                    + "S(F)(x)=sum_(n>=1) mobius(n)*n^4*F(n^2*x), and "
                    + "C=sum_(n>=1) n^(-3). For every originalPhysicalH6 source F, "
                    + "S(F) is again original H6. With M(F)=integral_(x>pi) "
                    + "(x/pi)^6*norm(F(x))^2, it satisfies M(S(F))<=C^2*M(F). "
                    + "Also T(S(F))=F and S(T(F))=F almost "
                    + "everywhere on x>pi. Both sides use the literal source series.")),
            Paragraph(Text(
                "In the exact application, the weighted-L2 norm of the double mode "
                    + "D_m D_n F=D_(mn) F is bounded by m^(-3)*n^(-3) times the "
                    + "source norm. The absolutely convergent L2 double family supplies "
                    + "almost-everywhere unconditional summability before any rearrangement. "
                    + "Grouping by mn then consumes the finite Mobius divisor identity "
                    + "from Mathlib and leaves only the first physical mode. The current "
                    + "Lean check pays these convergence and original-domain premises; "
                    + "they are not assumptions of the application. This reuses the "
                    + "existing dilation estimates and classical inversion, and adds "
                    + "no separate mathematical declaration. Its scope is the original "
                    + "sixth-moment space; full Gamma form domains and complete-energy "
                    + "positivity remain separate obligations.")),
            Describe.Lean(
                DescribeId.Create("actual-h6-full-theta-excess-bound"),
                DeclarationHandle.Create(Owner + "actual_h6_fullTheta_excess_bound"),
                H("The full theta transform preserves H6 and bounds the sixth-moment excess"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every original physical source F with originalPhysicalH6(F), "
                            + "the theorem proves all three clauses together: "
                            + "originalPhysicalH6(fullTheta(F)); genuine integrability on "
                            + "x>pi of ((x/pi)^6-1)*norm(fullTheta(F)(x))^2; and its "
                            + "integral at most C^2 times the same excess integral of F. "
                            + "Here C is the actual convergent series sum over j>=0 of "
                            + "(j+1)^(-3). The coefficient C is not replaced by a supplied "
                            + "finite constant. Since C=zeta(3)>1, this is a boundedness "
                            + "estimate; no strict contraction or optimality is claimed.")),
                    Paragraph(Text(
                        "The predicate originalPhysicalH6 means MemLp 2 on the original "
                            + "half-line x>pi together with genuine integrability of "
                            + "(x/pi)^6*norm(F(x))^2 there. The full transform retains every "
                            + "mode n^4 F(n^2 x), n=j+1>=1. No cutoff, independent "
                            + "coefficient model, assumed theta convergence, assumed excess "
                            + "bound or Gamma form-domain premise occurs in this statement.")),
                    Paragraph(Text(
                        "The proof uses the nonnegative densities (x/pi)^6-b "
                            + "for b=0 and b=1. Dilation by n^2 contributes the measure "
                            + "Jacobian n^(-2), and the sixth-moment scaling dominates the "
                            + "squared mode amplitude n^8. This yields the n^(-3) mode "
                            + "norm estimate in weighted L2. The b=0 estimate supplies H6 "
                            + "preservation, while b=1 gives the displayed excess bound. "
                            + "The L2 series is tied back to the literal fullTheta "
                            + "representative almost everywhere; a totalized sum alone "
                            + "does not serve as convergence evidence.")),
                    Paragraph(Text(
                        "Its mirrored audit keeps the complete F,hF telescope and all "
                            + "three conclusion clauses. It observes only the source excess "
                            + "integral on the right of the last bound. Replacing that "
                            + "readout by -1 fails at the lawful zero H6 source because "
                            + "C>0. Actual dependence is witnessed by zero and the H6 "
                            + "indicator of (2*pi,3*pi], whose excess is finite and positive. "
                            + "Both audits retain the original source states."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-h6-physical-term-summable-ae"),
                DeclarationHandle.Create(Owner + "actual_h6_physicalTerm_summable_ae"),
                H("The actual mode series is summable almost everywhere"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every F satisfying originalPhysicalH6(F), the theorem "
                            + "proves Summable(j -> physicalTerm(F,j,x)) for almost every "
                            + "x with respect to volume restricted to x>pi. It concerns "
                            + "the literal complex mode series, with the original F. It "
                            + "asserts no pointwise convergence on every x and supplies "
                            + "no convergence premise as an input.")),
                    Paragraph(Text(
                        "The weighted-L2 mode estimate makes the sum of mode "
                            + "norms finite. A function-space series result then supplies "
                            + "almost everywhere summability. Strict positivity of the "
                            + "b=0 density transfers that property to the original "
                            + "restricted volume measure.")),
                    Paragraph(Text(
                        "The mirrored law preserves the F,hF telescope, the original "
                            + "almost-everywhere filter and Summable. Its selected data "
                            + "operand is the entire partial application physicalTerm(F), "
                            + "a family indexed by j and x. The rejected constant-one "
                            + "mode family is nonsummable even at the lawful zero source; "
                            + "the half-line has nonzero measure. Actual dependence uses "
                            + "zero and the same H6 interval indicator, distinguished by "
                            + "mode j=0 at x=5*pi/2."))),
                DescribeRole.Theorem))));
}
