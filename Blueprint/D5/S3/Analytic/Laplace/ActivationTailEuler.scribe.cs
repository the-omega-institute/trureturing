using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Laplace;

internal sealed class ActivationTailEulerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual activation-tail calculus",
        H("ActivationTailEuler"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-tail-laplace-ode"),
                DeclarationHandle.Create("D5/S3/Analytic/Laplace/ActivationTailEuler.actual_tail_laplace_ode"),
                H("Actual activation-tail calculus"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any measurable real q integrable on u>u0 with u0>0, put k=q*(u+1)/u^2 and f(u)=-integral_(v>u) k(v). Weighted absolute Fubini proves both k and f integrable, absolute continuity on finite intervals and f prime=k almost everywhere. Every nonnegative moment of the actual cutoff transform converges for Re s>0. Dominated differentiation gives L prime and L double prime, and integration by parts gives s*L double prime+2*L prime=-Q prime+Q+U^2*f(U)*exp(-sU) for every U>=u0. The cutoff term has the positive sign. No continuation of actual integrals to a negative half-plane is asserted. The proof generalizes the activation-tail calculation using only source measurability and L1; the source need not be bounded."))), DescribeRole.Theorem))));
}
