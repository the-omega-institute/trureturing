using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class MembershipSeparatedOmissionsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/MembershipSeparatedOmissions";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Omissions with pairwise separation by nonsingleton membership classes.",
        H("Omitted Sets Distinguished by Membership"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("membership-separation"),
                DeclarationHandle.Create(Module + ".HasSeparatedMembership"),
                H("Distinguishing membership classes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each pair of distinct omitted sets differs on some class containing at least two distinct indices."
                    + " Indices in one class belong to exactly the same omitted sets."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("membership-separation-subfamily"),
                DeclarationHandle.Create(Module + ".mono"),
                H("Passage to a subfamily"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A pair of indices in one membership class still has the same membership after restricting to a subfamily."
                    + " A class distinguishing two retained sets still distinguishes them."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("membership-separation-intersection"),
                DeclarationHandle.Create(Module + ".inter_card_add_two_le"),
                H("Pairwise intersection bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two distinct members of equal cardinality share at most their size minus two indices."
                    + " The distinguishing class contributes two indices to the difference in one direction."
                    + " Equal cardinality gives the same bound in either direction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("private-pairs-separate-membership"),
                DeclarationHandle.Create(Module + ".of_private_pairs"),
                H("Private pairs give separation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A private pair belongs only to its own omitted set."
                    + " It therefore gives two indices with the same membership and distinguishes that set from any other."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("omission-multiplicities"),
                DeclarationHandle.Create(Module + ".omission_multiplicities"),
                H("Two bounds for the number of omissions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Consider r-element omissions with a common element in a K-element set."
                    + " Suppose distinct omissions intersect in at most r minus two elements."
                    + " Removing the common element, then deleting an index while avoiding one fixed coordinate, injects the petals into the (r minus two)-element subsets of the remaining K minus two indices."
                    + " Complementing the petals gives the other bound."
                    + " Thus the family has at most binom(K minus 2, r minus 2) and binom(K minus 2, r minus 1) members."))),
                DescribeRole.Theorem))));
}
