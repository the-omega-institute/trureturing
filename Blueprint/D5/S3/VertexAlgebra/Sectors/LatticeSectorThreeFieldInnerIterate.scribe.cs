using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeSectorThreeFieldInnerIterateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Sectors/LatticeSectorThreeFieldInnerIterate.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/VertexAlgebra/matsuo1997locality");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The same actual three-field numerator transports to the inner canonical iterate.",
        H("Three-Field Inner Iterate"), Blocks(
            Paragraph(Text("Take arbitrary even integral lattice data, three charges and arbitrary oscillator descendants u,v,t. The fields and inner iterate are the original canonical fields with their original cocycle. Rank zero, repeated charges and indefinite or degenerate Gram forms are included. No inverse Gram matrix or positive-energy assumption occurs.")),
            Describe.Lean(DescribeId.Create("actual-three-field-inner-iterate-transport"),
                DeclarationHandle.Create(Prefix + "actual_three_field_inner_iterate_transport"),
                H("One common numerator for six products and the inner iterate"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("One locality order k is chosen before the fourth charge delta and state w. The common-series theorem gives statewise cutoffs a and one generally infinite three-variable series P for all six original field orders. The theorem retains those same k,a,P and all six identities, and proves the inner canonical iterate identity at every signed exponent.")),
                    Paragraph(Text("After z1=t+z2, the complete clearing factor is z0^a0 (z0-t-z2)^k (z0-z2)^k t^k (t+z2)^a1 z2^a2. clearedInnerIterate expands this finite polynomial. The original iterate_borcherds law is passed through the outer canonical mode using its proven finite residue support. Statewise truncation bounds the residue fibers, finite sums commute, and signed_cleared_collision identifies the result with the native inner collision of exactly P.")),
                    Paragraph(Text("The negative first collision region is derived from common-numerator support, without enlarging k to bound an intermediate descendant. There is no uniform cutoff over all intermediate states, no cancellation of the full clearing factor on unrestricted distributions, and no finiteness assumption on P. This is one inner collision; a second collision, final Laurent transport, associators, pentagon, hexagon and sewing remain further obligations.")),
                    Paragraph(Text("The Bakalov-Kac, Matsuo-Nagatomo and Carnahan sources remain those of the imported lattice, locality and binomial suppliers. This formal coefficient theorem does not establish analytic CFT, Monster realization, string theory or AdS/CFT."))), DescribeRole.Theorem))));
}
