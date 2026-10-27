// Blueprint source for ordinary integrability of the complete selected-domain responses.
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class AutomaticCubicResponseIntegrabilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/AutomaticCubicResponseIntegrability.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordinary integrability of both complete selected-domain responses follows from the original bounds and explicit moving-center formulas.",
        H("Ordinary Integrability of the Complete Actual and Cubic Responses"),
        Blocks(
            Paragraph(Text(
                "The theorem complete_selected_responses_integrable supplies "
                + "the two ordinary response-integrability premises required for "
                + "integrating a cubic replacement estimate, using only the "
                + "existing original bounds and the complete selected domain.")),
            Describe.Lean(
                DescribeId.Create("complete-selected-responses-integrable"),
                DeclarationHandle.Create(Prefix + "complete_selected_responses_integrable"),
                H("The original bounds suffice for both response integrals"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take OriginalFirstClockTransport.OriginalWindow X, real "
                        + "ell and R, ell>=243, and OriginalBounds X ell R. Put "
                        + "S=selectedDomain X, H(t)=windowLength t=t^(4/5), "
                        + "d(t)=normalization t=t^(11/10), "
                        + "lambda(t)=g(t)=1/(t log(t)), and "
                        + "w(t)=activationDensity t=(log(t)+1)/(t^2 log(t)^2). "
                        + "There are no other hypotheses: in particular, no prime-mass, "
                        + "prime-distribution or response-integrability premise.")),
                    Paragraph(Text(
                        "The conclusion is the conjunction "
                        + "IntegrableOn (fun t => canonicalActualPrimeResponse R t "
                        + "(windowLength t) (normalization t)) S and "
                        + "IntegrableOn (fun t => cubicPrimeResponse R t "
                        + "(windowLength t) (normalization t)) S, for real-valued "
                        + "functions and Lebesgue measure. S remains the complete "
                        + "union of original good consecutive-label closed edges, "
                        + "with overlaps counted once. The least full-domain sources "
                        + "over positive multiples of 5040p and the original strict "
                        + "inventories are unchanged; no edge is removed or shortened.")),
                    Paragraph(Text(
                        "The actual response is the finite sum over prime "
                        + "q<=floor(2R) of log(q) times the literal actualKernel at "
                        + "firstClock q, minus continuumExact. The cubic response "
                        + "uses the same finite prime inventory, the active condition "
                        + "t<firstClock q<=t+H, the existing cubicOffset, and the "
                        + "complete three-term cubicCenter. These are the existing "
                        + "ThirdOrderPrimeKernel response definitions, rather than "
                        + "new surrogate responses or a leading-term center.")),
                    Paragraph(Text(
                        "For the actual prime atoms, the proof reuses the private "
                        + "OriginalFirstClockTransport.original_kernel_integrable "
                        + "supplier and actual_eq_reference_on_domain. Multiplication "
                        + "by log(q), equality on S and finite summation supply the "
                        + "integrability of the literal actual prime sum. The "
                        + "actualKernel initial endpoint is preserved by the existing "
                        + "actual/reference identity on the original selected domain.")),
                    Paragraph(Text(
                        "The new moving-center calculation uses the exact primitive "
                        + "integral_(0..H) lambda(t+u) du "
                        + "=log(log(t+H))-log(log(t)) for t>1 and H>=0. Hence "
                        + "continuumExact(t,H,d) "
                        + "=[log(log(t+H))-log(log(t))-H lambda(t+H)]/[w(t)d]. "
                        + "On S the original bounds give t>=ell>=243; continuity "
                        + "of the formula and positivity of w(t)d establish "
                        + "continuity on the existing compact domain, and therefore "
                        + "ordinary integrability of this exact continuum center.")),
                    Paragraph(Text(
                        "For each cubic prime atom, continuity of w, w', w'', H "
                        + "and d, together with nonvanishing denominators on S, "
                        + "gives a continuous coefficient "
                        + "log(q)*cubicOffset(t,H(t),d(t),firstClock(q)-t). The set "
                        + "{t : t<firstClock q and firstClock q<=t+H(t)} is measurable: "
                        + "its first condition is open and its second is a closed "
                        + "inequality between continuous functions. Its indicator "
                        + "preserves integrability on compact S. The same coefficient "
                        + "continuity proves integrability of cubicCenter, so finite "
                        + "summation and subtraction produce the second response.")),
                    Paragraph(Text(
                        "The new proof work is the moving continuum closed form, "
                        + "its continuity, and the measurable moving-threshold "
                        + "argument for the cubic atoms and center. The compact "
                        + "domain, original bounds, actual/reference transport, "
                        + "reference-kernel integrability and density derivative "
                        + "suppliers are reused from the existing repository. This "
                        + "is a classical-calculus and measure-theory derivation, "
                        + "with no literature-priority claim.")),
                    Paragraph(Text(
                        "Ordinary integrability alone supplies no prime-mass "
                        + "estimate, no favorable signed main term, no EL.14 bound "
                        + "and no RH or unrestricted Robin conclusion. It is also "
                        + "not a weighted zero-sampling or noncompact Fourier "
                        + "integrability theorem."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Arith/Robin/ThirdOrderPrimeKernel")),
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Arith/Robin/OriginalFirstClockTransport")),
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Arith/Robin/ActualRobinClockCovariance"))
        ]));
}
