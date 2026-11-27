using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuOneModeCubicDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuOneModeCubic.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonnegativity of the one-mode cubic spectral deficit at every r ≥ 1.",
        H("The one-mode cubic bound"),
        Blocks(
            Describe.Lean(DescribeId.Create("one-mode-bound"), DeclarationHandle.Create(Owner + "one_mode_bound"),
                H("Nonnegativity of the one-mode deficit"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Wu),
                Blocks(
                    Paragraph(Text("The cubic coefficient is the p = 3 specialization of Wu v1, Theorem 3.1, eq. (3.4), with Gibbs ratio r = exp(β/3). It agrees with the coefficient in Remark 3.15, eqs. (3.54)–(3.55), including the tracial value 1/2 at r = 1. For every r ≥ 1, the exact spectral premise OneModeBound r says that oneModeDeficit r v w z is nonnegative for all 0 ≤ v ≤ w and −1 ≤ z ≤ 1, where z is the upper eigenvector’s Bloch coordinate.")),
                    Paragraph(Text("For 0 < v < w, completing the square in z reduces the proof to a scalar function of t = w/v. Comparing secant slopes of a strictly convex function of log t gives the sign of the scalar derivative on either side of t = r, where the scalar function attains its minimum of zero. At r = 1 the comparison uses the tangent slope at log t = 0. Continuity of x log x extends the deficit bound to v = 0 and v = w, with v = w = 0 checked directly."))),
                DescribeRole.Theorem),
            Paragraph(Text("For r ≥ 1, a unitary two-mode frame U and spectrum (m, n, n, 1) with 0 ≤ m ≤ n ≤ 1, pass one_mode_bound hr as the OneModeBound r argument of repeated_middle_lower_bound. The weighted sum of the two Hölder gaps and the frame remainder are each nonnegative, and their sum lower-bounds sourceDeficit r U m n in these spectral coordinates.")))));
}
