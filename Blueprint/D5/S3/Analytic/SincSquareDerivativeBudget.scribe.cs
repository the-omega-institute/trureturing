using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class SincSquareDerivativeBudgetDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/SincSquareDerivativeBudget.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive integral recurrence bounds every derivative of an entire squared-sinc endpoint profile.",
        H("An entire endpoint profile with factorial derivative budgets"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sincsquarederivativebudget-psi"),
                DeclarationHandle.Create(Prefix + "psi"),
                H("The entire cosine square-root extension"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Estimation/nist2026trigonometricseries")),
                Blocks(Paragraph(Text("For every real t, psi(t) is the everywhere convergent series sum_k (-1)^k t^k/(2k)!. For t >= 0 it equals cos(sqrt(t)), including psi(0)=1. The series defines the function also for negative t."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sincsquarederivativebudget-endpoint"),
                DeclarationHandle.Create(Prefix + "endpoint"),
                H("The entire endpoint profile"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Estimation/nist2026trigonometricseries")),
                Blocks(Paragraph(Text("For every real eta and t, endpoint(eta,t) is the series sum_k 2(-1)^k(8/eta)^k t^k/(2k+2)!. Real division is total; the estimates below require eta > 0. For positive t and eta it equals 2[1-cos(sqrt(8t/eta))]/(8t/eta), or sinc(sqrt(2t/eta)) squared."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sincsquarederivativebudget-endpoint-budget"),
                DeclarationHandle.Create(Prefix + "endpoint_budget"),
                H("One profile satisfies all endpoint constraints"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/nist2026trigonometricseries")),
                Blocks(Paragraph(Text("For every eta > 0, endpoint eta is infinitely differentiable on the entire real line, has value 1 at zero, is nonnegative for every t >= 0, and is at most eta/2 for every t >= 1. Simultaneously, for every natural n and every t >= 0, |D^n endpoint(eta,t)|/n! <= (8/eta)^n/(2n)!. The recurrence D^(n+1) psi(t) = -(1/2) integral_0^1 r^(2n) D^n psi(r^2 t) dr preserves the oscillatory cancellation; its kernel mass gives n!/(2n)!. The triangular cosine integral then transfers that budget to the endpoint profile."))),
                DescribeRole.Theorem))));
}
