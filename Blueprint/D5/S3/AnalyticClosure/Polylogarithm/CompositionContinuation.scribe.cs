using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.AnalyticClosure.Polylogarithm;

internal sealed class CompositionContinuationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/AnalyticClosure/Polylogarithm/CompositionContinuation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Recursive segment integrals define the positive-composition slit branches.",
        H("CompositionContinuation"), Blocks(
            Describe.Lean(DescribeId.Create("slit-segment-primitive"),
                DeclarationHandle.Create(Prefix + "starPrimitive"),
                H("Attributed segment integral"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/AnalyticClosure/li2026starprimitive")),
                Blocks(Paragraph(Text(
                    "The segment integral from p to z is copied from Will (Ziang) Li's immutable "
                    + "RiemannDynamics core. The Lean module retains the exact upstream LICENSE, "
                    + "copyright, attribution, extraction notice and own-pinned-Mathlib retirement "
                    + "condition. Its primitive proof remains local in the actual source consumer."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("constructed-composition-branch"),
                DeclarationHandle.Create(Prefix + "continued"),
                H("The actual continued family"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/AnalyticClosure/xu2026rational"),
                    LibraryNoteRef.Create("D5/L/AnalyticClosure/li2026starprimitive")),
                Blocks(Paragraph(Text(
                    "omega is the full set of complex z with 1-z in Complex.slitPlane. "
                    + "The empty composition is the constant one. For a nonempty composition, "
                    + "raise first integrates the tail branch divided by 1-z, then integrates "
                    + "dslope repeatedly to raise the leading exponent. dslope uses the derivative "
                    + "at zero. These definitions assume neither source continuation nor a "
                    + "recurrence or convergence assertion outside the disk."))), DescribeRole.Definition))));
}
