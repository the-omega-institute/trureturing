using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.AnalyticClosure.Polylogarithm;

internal sealed class CompositionSlitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive-composition source series has its normalized holomorphic branch on the full slit domain.",
        H("CompositionSlit"), Blocks(
            Describe.Lean(DescribeId.Create("source-faithful-slit-continuation"),
                DeclarationHandle.Create("D5/S3/AnalyticClosure/Polylogarithm/CompositionSlit.result"),
                H("All positive compositions on the full slit domain"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/AnalyticClosure/xu2026rational"),
                    LibraryNoteRef.Create("D5/L/AnalyticClosure/li2026starprimitive")),
                Blocks(Paragraph(Text(
                    "The recursively defined continued family is holomorphic on omega={z:1-z "
                    + "belongs to Complex.slitPlane}, which excludes the real ray [1,infinity). "
                    + "The empty word equals one. Every nonempty positive composition vanishes "
                    + "at zero, agrees with the actual strict nested source series on |z|<1, "
                    + "has exact zero order equal to its depth, and commutes with conjugation.")),
                    Paragraph(Text(
                    "For leading one, the derivative is the continued tail divided by 1-z. "
                    + "For leading exponent greater than one it is the predecessor branch divided "
                    + "by z off zero; at zero the derivative is one for an empty tail and zero "
                    + "otherwise. The proof establishes openness and star convexity of omega, "
                    + "constructs removable integrands using Mathlib's dslope theorem, and applies "
                    + "the attributed primitive on the live nested induction path. The frozen "
                    + "source recurrences and normalization identify the disk germ; analytic "
                    + "identity extends both recurrences and conjugation on the connected domain.")),
                    Paragraph(Text(
                    "This intermediate source bridge receives zero solved-problem credit. It "
                    + "does not assert global slit nonvanishing, admissible boundary summability, "
                    + "MZV limits, bank estimates, a zero-free collar or coefficient-sign transfer. "
                    + "Xu-Zhao Conjecture 1.3 remains open. The classical primitive is a local "
                    + "attributed supplier, with no standalone generic theorem claim."))), DescribeRole.Theorem))));
}
