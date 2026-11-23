using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class PrivatePairOmissionFamilyDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/PrivatePairOmissionFamily";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Private elements and the intersections of omitted sets.",
        H("Private Pairs in Omission Families"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hasprivatepairs"),
                DeclarationHandle.Create(Module + ".HasPrivatePairs"),
                H("Private pairs"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every member of a finite family of finite sets contains two distinct elements that belong to no other member."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hasprivatepairs-mono"),
                DeclarationHandle.Create(Module + ".mono"),
                H("Restriction to a subfamily"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Any subfamily inherits the two private elements of each of its members."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hasprivatepairs-of-disjoint-petals"),
                DeclarationHandle.Create(Module + ".of_disjoint_petals"),
                H("Pairs in disjoint petals"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If erasing a fixed element leaves pairwise disjoint sets of size at least two, two elements from each erased set give private pairs for the original family."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hasprivatepairs-inter-card-add-two-le"),
                DeclarationHandle.Create(Module + ".inter_card_add_two_le"),
                H("Intersection bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The intersection of two distinct members, together with two private elements of the first, lies inside the first member."
                    + " Thus the intersection has at most the first member's cardinality minus two elements."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hasprivatepairs-erase-exists"),
                DeclarationHandle.Create(Module + ".erase_exists"),
                H("Erasing a common element"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume each member has a private pair, the fixed element belongs to every member, and each erased set has size at least two."
                    + " Every erased set admits two private elements."
                    + " For a family of at least two members the original private elements survive erasure."
                    + " For one member any two remaining elements suffice."))),
                DescribeRole.Theorem))));
}
