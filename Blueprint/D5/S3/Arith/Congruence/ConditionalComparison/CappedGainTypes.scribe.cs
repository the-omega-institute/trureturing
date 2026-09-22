using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence.ConditionalComparison;

internal sealed class CappedGainTypesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Schroeder's geometric saturation bound for injectively indexed nonzero cofactor types.",
        H("Full-Type Geometric Saturation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("full-type-saturation"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Congruence/ConditionalComparison/CappedGainTypes.saturation_bound"),
                H("Each nonzero type has total geometric weight at most one"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Arith/schroeder2026noncoverage")),
                Blocks(
                    Paragraph(Text(
                        "This is a source transplant of Michael Schroeder's "
                        + "Erdos7.CappedGain.saturation_bound. Its copyright, "
                        + "full MIT license and source correspondence appear in "),
                        Ref("D5/L/Arith/schroeder2026noncoverage"), Text(".")),
                    Paragraph(Text(
                        "Let A be an arbitrary finite label family, I any finite "
                        + "index type with a distinguished zero, and p a rational "
                        + "number at least one. Assume the pair of index and "
                        + "depth is injective on A, every index is nonzero, and "
                        + "every depth lies between one and an arbitrary finite "
                        + "bound D. The sum of beta(p, depth), where beta(p,e) "
                        + "is (p-1)/p^e, is at most the cardinality of I minus one.")),
                    Paragraph(Text(
                        "The proof embeds the family into nonzero index-depth "
                        + "pairs and sums the finite geometric series in each "
                        + "index fiber. It imposes no sparsity condition on the "
                        + "index type. For a product of bounded exponent sets, "
                        + "the ordinary Mathlib cardinality theorem supplies "
                        + "the product of the coordinate sizes directly inside "
                        + "an application. No specialized cofactor wrapper is "
                        + "added by this transplant."))),
                DescribeRole.Theorem))));
}
