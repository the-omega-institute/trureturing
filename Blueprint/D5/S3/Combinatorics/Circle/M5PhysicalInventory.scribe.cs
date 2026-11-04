using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class M5PhysicalInventoryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Physical occurrences and the W_J prefix.",
        H("Physical occurrences and the W_J prefix"),
        Blocks(
            Paragraph(Text("SourcePrefixInventory owns the common seven-row prefix, row-mask disjointness and bank-charge proofs. Here the seven roles embed into Fin(10), and the M5 row data extends that shared record with its three remaining parents, actual tail recurrence and total conservation. The physical map, complete ten-row inventory and M5 T selection remain here; their prefix calls use the shared owner directly.")),
            Paragraph(Text("The occurrence domain is the disjoint sum of ten parent labels and the dependent pairs (row,index) for every literal SMALL row position. Its map to Fin(k) is injective and exhaustive by the original source partition. Equal source values do not identify occurrences.")),
            Paragraph(Text("A legal prefix contains each member of its used Finset once, starts with the designated x label, and has every partial sum in [0,C]. SMALL batches extend such a prefix when their actual total endpoint lies in the strip, using the existing SMALL scheduling theorem and the bound |s|<=Q-1.")),
            Paragraph(Text("Select retained n and w masks of weights A and P0-A. The initial SMALL batch is the full b1 row together with their complementary masks. The word begins x,d,beta, then this batch, then gamma,P,J. Its height is Z=f+P+J. The old bank consists exactly of retained n,w labels and the full z,b,v rows. The identity 2*(Z+charge(bank))=z-u links this physical bank to the T gate."))), []));
}
