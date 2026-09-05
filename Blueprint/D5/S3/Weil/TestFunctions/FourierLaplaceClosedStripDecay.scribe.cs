using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.TestFunctions;

internal sealed class FourierLaplaceClosedStripDecayDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/TestFunctions/FourierLaplaceClosedStripDecay.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Fourier-Laplace closed-strip bound has a specific two-jet constant, bounded by finite unweighted L1 enclosures and the support radius.",
        H("Fourier-Laplace Closed-Strip Decay"),
        Blocks(
            Describe.Lean(DescribeId.Create("fourier-laplace-closed-strip-jet-budget"),
                DeclarationHandle.Create(Prefix + "closedStripJetBudget"),
                H("Explicit weighted two-jet constant"),
                StatementSource.FromAuthor(Disp(F.Id("D_eta(g)=integral exp(eta*|x|)|g(x)| + integral exp(eta*|x|)|g second derivative(x)|."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This is the precise constant produced by the existing two integrations by parts. No convergence-neighborhood choice occurs."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("fourier-laplace-closed-strip-jet-spec"),
                DeclarationHandle.Create(Prefix + "closedStripJetBudget_spec"),
                H("The named constant satisfies the original bound"),
                StatementSource.FromAuthor(Disp(F.Id("For eta>=0, D_eta>=0 and |FT(g)(w)|<=D_eta/(1+Re(w)^2) on |Im(w)|<=eta."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing integration-by-parts proof is retained and exposes its actual weighted zeroth and second derivative integrals."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fourier-laplace-decay-closed-strip"),
                DeclarationHandle.Create(Prefix + "fourierLaplace_decay_closedStrip"),
                H("Uniform quadratic decay on every closed strip"),
                StatementSource.FromAuthor(Disp(F.Id("For every eta>=0 there exists C>=0 such that |FT(g)(w)|<=C/(1+Re(w)^2) throughout the closed strip."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original public existential statement is preserved as an application of the named constant theorem."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fourier-laplace-closed-strip-support-jets"),
                DeclarationHandle.Create(Prefix + "closedStripJetBudget_le_support_jets"),
                H("Support and finite seminorm enclosures"),
                StatementSource.FromAuthor(Disp(F.Id("Support in [-B,B], eta>=0, integral |g|<=J0 and integral |g second derivative|<=J2 imply D_eta(g)<=exp(eta*B)*(J0+J2)."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Derivative topological supports lie in the original support. Bound each exponential weight on that closed interval, compare the integrals and add."))), DescribeRole.Theorem)), []));
}
