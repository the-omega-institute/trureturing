using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class RankThreeInternalSizeSpectrumDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/RankThreeInternalSizeSpectrum";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact range of sizes of internal extensions follows from a finite packing problem in each residue class.",
        H("Attainable Numbers of Internal Triples"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("packing-number"),
                DeclarationHandle.Create(Module + ".packingNumber"),
                H("The packing number on a finite label set"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The packing number is the maximum size of a family of three-element label sets in which each pair of distinct labels occurs in at most one member. The empty family is allowed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("size-spectrum"),
                DeclarationHandle.Create(Module + ".exact_size_spectrum"),
                H("The full interval of attainable sizes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix positive row dimension and class size, the lifted pair-unique family of zero-sum triples on distinct rows covering every cross-row pair. Label each actual residue class by Fin r using the uniform residue indexing. Add unordered triples of three distinct points within rows, preserving pair uniqueness and normalized potential dimension one more than the row dimension.")),
                    Paragraph(Text("The lower endpoint is the number of Latin cells across all rows. The upper endpoint adds the packing number times the number of row and residue-class pairs. Every integer between the endpoints occurs.")),
                    Paragraph(Text("The unordered blocks split into the Latin cells and disjoint transported packing families. For the upper bound, each class contributes at most the packing number. For attainability, put a maximum pack in each class and choose an arbitrary subset of the union of these packing blocks. Each class remains a valid partial Steiner system, so the realization theorem preserves the required dimension."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("internal-extension"),
                DeclarationHandle.Create(Module + ".IsInternalExtension"),
                H("Dimension-preserving internal extensions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An internal extension is the unordered family of distinct-point triples added within rows. The combined family uses each point pair at most once and has normalized ternary potential dimension one more than the row dimension."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("saturated-extension"),
                DeclarationHandle.Create(Module + ".IsSaturatedInternalExtension"),
                H("Saturated internal extensions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A compatible extension is saturated if every compatible extension that contains it is equal to it."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("insert-extension"),
                DeclarationHandle.Create(Module + ".internal_extension_insert"),
                H("A triple from a larger extension can be added on its own"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fix the lifted cross-row family satisfying pair uniqueness. For compatible internal extensions ordered by inclusion, any triple in the larger family can be adjoined to the smaller while preserving the dimension. The two families determine the same rowwise Latin squares. An added triple enlarges one partial Steiner system by a block from the corresponding larger system."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("saturation-by-class"),
                DeclarationHandle.Create(Module + ".saturated_internal_extension_iff"),
                H("Saturation in each residue class"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the same mixed-family hypotheses and any labelling preserving the actual residue, an internal extension is saturated exactly when its decomposition consists of Latin squares and inclusion-maximal partial Steiner systems in every row and residue class. Any proper compatible enlargement changes at least one class, and every local enlargement gives a compatible global enlargement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("saturated-six-sizes"),
                DeclarationHandle.Create(Module + ".saturated_six_size_spectrum"),
                H("The saturated sizes with six labels in each class"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix positive row dimension d, cyclic size eighteen, and a pair-unique lifted mixed family with distinct rows in each triple and zero-sum completion of every cross-row pair. The saturated numbers of unordered internal triples are 36 times 3 to the power d, plus 2 times 3 to the power d+1, plus 2k, for k between zero and 3 to the power d+1.")),
                    Paragraph(Text("An exhaustive finite certificate checks that the maximal packings on six labels have either two or four blocks. Both sizes occur. Each residue class contributes two blocks and can independently contribute two more. The Latin squares contribute 36 blocks per row."))),
                DescribeRole.Theorem))));
}
