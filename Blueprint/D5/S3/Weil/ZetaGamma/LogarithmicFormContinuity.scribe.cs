using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma;

internal sealed class LogarithmicFormContinuityDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaGamma/LogarithmicFormContinuity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Logarithmically weighted square error controls the quadratic integral of the actual completed-zeta Gamma symbol.",
        H("Continuity of the actual Gamma quadratic integral"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-gamma-quadratic-log-weight-continuity"),
                DeclarationHandle.Create(Owner + "actual_gamma_quadratic_tendsto_of_log_weight_error"),
                H("Weighted error controls the actual Gamma quadratic limit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let alpha be any type, l any filter on alpha, U a continuous "
                        + "complex-valued function on the real frequency line, and V a family "
                        + "of such functions. Write w(t)=1+log(1+|t|), W(F)=(1/(2*pi))*"
                        + "integral w(t)*|F(t)|^2 dt, and Q(F)=(1/(2*pi))*integral "
                        + "(2*pi*Zeta23.mu(t))*|F(t)|^2 dt. The Gamma symbol is exactly "
                        + "Re digamma(1/4+i*t/2)-log(pi), using the existing definition of mu.")),
                    Paragraph(Text(
                        "Assume w*|U|^2 is integrable, V(a) is continuous eventually along l, "
                        + "and w*|V(a)-U|^2 is integrable eventually along l. If W(V(a)-U) "
                        + "tends to zero along l, then Q(V(a)) tends to Q(U) along l. "
                        + "The theorem imposes no nontrivial-filter, compact-support, parity, "
                        + "or spatial Fourier-identification hypothesis. Its objects are the "
                        + "displayed frequency profiles and actual Gamma-weighted integrals.")),
                    Paragraph(Text(
                        "The proof consumes the repository's actual digamma strip growth "
                        + "bound to obtain |2*pi*mu(t)|<=C*w(t). It establishes actual Gamma "
                        + "square and mixed-term integrability before using integral additivity. "
                        + "Mathlib's parameterized Young inequality bounds the actual Hermitian "
                        + "mixed term. Expanding the square then gives, for every delta>0, "
                        + "|Q(U+E)-Q(U)|<=C*((1+delta^(-1))*W(E)+delta*W(U)). First choose "
                        + "delta for the fixed target and then use the assumed weighted-error "
                        + "limit. Growth, mixed estimates, and integral expansion are consumed "
                        + "helpers of this single public continuity conclusion.")),
                    Paragraph(Text(
                        "The intended same-window application supplies U and V from the "
                        + "actual target and smooth-trial Fourier profiles. This theorem "
                        + "requires their continuity, actual weighted integrability, and "
                        + "weighted-error limit to be established separately. In particular, "
                        + "it does not itself prove that prepared same-window weighted-error "
                        + "estimate, construct a closed form or a form core, identify a "
                        + "Neumann resolvent, pass an infinite boundary mixture, or prove RH."))),
                DescribeRole.Theorem))));
}
