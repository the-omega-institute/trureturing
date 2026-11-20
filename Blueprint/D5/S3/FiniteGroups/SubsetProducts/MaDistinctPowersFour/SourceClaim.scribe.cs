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
                Blocks(Paragraph(Text("The registered proposition ranges over every positive n and every finite group, with the class-size bound four."))),
                DescribeRole.Definition))));
}
