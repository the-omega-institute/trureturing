using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour;

internal sealed class MaSourceClaimDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ma's order exclusions, generator classes and distinct-power enumeration.",
        H("Ma's order exclusions, generator classes and distinct-power enumeration"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ma-sourceclaim-generatorclass"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/SourceClaim.generatorClass"),
                H("generatorClass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/FiniteGroups/ma2026distinctpowers")),
                Blocks(Paragraph(Text("The subtype of elements of the finite set A that generate the same subgroup as x."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ma-sourceclaim-nosmallorders"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/SourceClaim.noSmallOrders"),
                H("noSmallOrders"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/FiniteGroups/ma2026distinctpowers")),
                Blocks(Paragraph(Text("Every element of G avoids each order from 2 through n + 1, inclusive."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ma-sourceclaim-classesatmostfour"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/SourceClaim.classesAtMostFour"),
                H("classesAtMostFour"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/FiniteGroups/ma2026distinctpowers")),
                Blocks(Paragraph(Text("The bound is evaluated for every representative in A."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ma-sourceclaim-hasdistinctpowersenumeration"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/SourceClaim.hasDistinctPowersEnumeration"),
                H("hasDistinctPowersEnumeration"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/FiniteGroups/ma2026distinctpowers")),
                Blocks(Paragraph(Text("An equivalence enumerates A once and the index plus one is its exponent."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ma-sourceclaim-claim"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/SourceClaim.claim"),
                H("claim"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/FiniteGroups/ma2026distinctpowers")),
                Blocks(
                    Paragraph(Text(
                        "Ma asks in Remark 2.2 (p. 3), “It remains open whether an analogous general theorem holds "
                        + "when the equivalence classes have size at most 4.” "
                        + "Section 9 (p. 16) repeats the question: “More generally, it would be interesting to know "
                        + "whether the hypothesis ‘size at most 3’ in Theorem 1.1 can be replaced by ‘size at most 4’.”")),
                    Paragraph(Text(
                        "The proposition keeps the other hypotheses of Theorem 1.1 (p. 1). "
                        + "The subset has positive cardinality n, and no group element has order from 2 through n + 1. "
                        + "An equivalence from Fin n enumerates the subset, with exponent one plus the index."))),
                DescribeRole.Definition))));
}
