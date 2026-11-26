using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class OriginalHalfBinomialProjectiveDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal original complementary period ratio has a nonzero derivative and an exact Schwarzian on the entire open lens.",
        H("The native period-ratio Schwarzian"),
        Blocks(Describe.Lean(DescribeId.Create("original-tau-projective"),
            DeclarationHandle.Create("D5/S3/Analytic/OriginalHalfBinomialProjective.original_tau_projective"),
            H("Actual third-order regularity and exact Schwarzian"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/nist2010schwarzian")),
            Blocks(
                Paragraph(Text("For every complex r with norm r<1 and norm(1-r)<1, let "
                    + "P be the literal original half-binomial-square period and tau(r)=iP(1-r)/P(r), "
                    + "exactly as defined in OriginalHalfBinomialWronskian. Its actual derivative is "
                    + "nonzero. The theorem gives an actual derivative of tau', differentiability "
                    + "of tau'', and g=tau''/tau'=-(1-2r)/(r(1-r))-2P'/P. It proves "
                    + "S(tau)=(1-r+r squared)/(2r squared(1-r) squared).")),
                Paragraph(Text("The generic inference is instantiated with A=r(1-r), "
                    + "p=(1-2r)/A, q=-1/(4A), W=-i/(pi A), y=P and the actual tau. "
                    + "The native Picard-Fuchs theorem provides both differentiability conclusions "
                    + "and the ODE. The proved disk nonvanishing and the lens inequalities exclude "
                    + "all denominator zeros. Rational differentiation proves W'=-pW internally; "
                    + "the existing exact tau derivative identifies W/P squared. No extra ODE, "
                    + "regularity or nonvanishing hypotheses are imposed at the endpoint.")),
                Paragraph(Text("The canonical FiniteMode Gaussian period correction consumes the "
                    + "actual quotient formula. This local result does not assert continuation, "
                    + "monodromy, global uniformization, positivity, operator transport or a physical geometry."))),
            DescribeRole.Theorem))));
}
