using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Orthogonality;

internal sealed class SixBitLineChromaticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The independent six-dimensional line graph result.",
        H("The full weighted inequality and the original twelve-color witness"),
        Blocks(
            Describe.Lean(DescribeId.Create("six-line-weight-check"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitLineChromatic.weight_check"),
                H("Complete weighted check"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("Kernel reduction evaluates the complete include-or-omit recursion on all63 nonzero masks, using weight3 for even and4 for odd. The checked value19 supplies the numerical premise of the general soundness theorem; no sampled subsets or encoded answer premise are used."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("six-line-weighted-bound"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitLineChromatic.weighted_bound"),
                H("Every independent set"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("Every finite subset avoiding zero and having nonzero dot product on every distinct pair has total weight at most19. This is exactly the full source independent-set domain."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("six-line-independence-profile"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitLineChromatic.independence_profile"),
                H("Parity and extremal size"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("With t even and o odd members,3t+4o<=19 and size<=6. A size-six class has exactly five even and one odd member. A second complete restricted check bounds any all-even independent set by five."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("six-line-coloring-lower-bound"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitLineChromatic.coloring_lower_bound"),
                H("Every coloring needs twelve colors"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The31 nonzero even and32 odd vectors have total weight221. Every actual color fiber has weight at most19, and an exact finite fiber sum gives221<=19k for every k-coloring. Hence k>=12."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("six-line-result"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitLineChromatic.result"),
                H("The exact line chromatic number"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The original twelve literal classes define a coloring of all63 nonzero masks, checked on every distinct orthogonality pair. Combined with the universal weighted lower bound, the actual six-bit line graph has chromatic number12. A separate full coordinate/Submodule representation bridge remains necessary for target transport; the theorem does not establish the all-subspace answer15 or any n7 upper bound."))), DescribeRole.Theorem))
        , [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/Orthogonality/WeightedIndependentBound"))]));
}
