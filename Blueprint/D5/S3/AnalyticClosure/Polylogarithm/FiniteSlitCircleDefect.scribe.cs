using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.AnalyticClosure.Polylogarithm;

internal sealed class FiniteSlitCircleDefectDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitCircleDefect.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual patched outer Cauchy contribution is integrable and obeys the same source bound for every natural index.",
        H("FiniteSlitCircleDefect"), Blocks(
            Describe.Lean(DescribeId.Create("patched-integrand"), DeclarationHandle.Create(Prefix + "outerIntegrand"),
                H("The single cut point"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/AnalyticClosure/xu2026rational")),
                Blocks(Paragraph(Text("For A : Complex to Complex, real R and natural n, the integrand is zero at z=R and A(z)/z^(n+1) elsewhere."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-outer-coefficient"), DeclarationHandle.Create(Prefix + "outerCoefficient"),
                H("The positively oriented outer contribution"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/AnalyticClosure/xu2026rational")),
                Blocks(Paragraph(Text("outerCoefficient is the actual circle integral of outerIntegrand about zero with radius R, multiplied by the inverse of 2 pi i."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("logarithmic-pullback"), DeclarationHandle.Create(Prefix + "upperPullback"),
                H("The logarithmic pullback"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/AnalyticClosure/xu2026rational")),
                Blocks(Paragraph(Text("upperPullback P n w equals P(exp w)/(exp w)^n. The exponent n retains the cancellation of one denominator power by the exponential Jacobian."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("upper-rectangle-balance"), DeclarationHandle.Create(Prefix + "upperRectangleBalance"),
                H("The oriented upper rectangle"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/AnalyticClosure/xu2026rational")),
                Blocks(Paragraph(Text("upperRectangleBalance is the exact equation bottom minus top plus i times right minus i times left equals zero, for upperPullback on the rectangle from log(1/2) to log(R) and from angle zero to pi."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("same-witness-outer-control"), DeclarationHandle.Create(Prefix + "result"),
                H("All compositions and all natural indices"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/AnalyticClosure/xu2026rational")),
                Blocks(
                    Paragraph(Text("Every positive head, finite positive-entry tail and positive ell has the SAME R0, rho, R, upper and B supplied by FiniteSlitCompositionMoments.result. The actual reciprocal is analytic on the slit disk, agrees with the original normalized disk reciprocal and retains its removable value at zero. The upper bank extends it continuously to the closed upper half disk of radius R. The extension equals the reciprocal on omega and the same bank on the cut.")),
                    Paragraph(Text("For every natural n, including zero, the patched outer integrand is CircleIntegrable, the imaginary bank moment is IntervalIntegrable from 1 to R, and norm(outerCoefficient)<=B/R^n. The bound uses the original B, independent of n. Analytic continuity off the single cut point proves angular measurability; the sphere bound then proves actual integrability. The circle norm theorem gives the stated exact bound.")),
                    Paragraph(Text("The extension is pasted across two closed sets separated by delta=(rho+R-1)/2. The far set lies in omega; the near set uses upper-bank continuity. Their overlap agrees by the actual bank matching law.")),
                    Paragraph(Text("For every natural n the extension also satisfies upperRectangleBalance. Its proof applies rectangular Goursat to the constructed continuous extension; in the open rectangle the exponential image has positive imaginary part and the pullback is analytic. The full-circle finite-slit coefficient identity and its relation to iterated derivatives remain unproved here. No source coefficient sign follows from this result alone. Exact ordinary formal-inverse realization, all fixed positive j and the strict admissible binomial lower bound remain separate obligations. The full Xu--Zhao problem remains open."))),
                DescribeRole.Theorem))));
}
