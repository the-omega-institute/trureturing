using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class MixedDyadicAugmentationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At most two fresh labels augment every native legal word.",
        H("At most two fresh labels augment every native legal word"),
        Blocks(
            Describe.Lean(DescribeId.Create("dyadic-package-mixeddyadicaugmentation"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/MixedDyadicAugmentation.native_two_fresh_augmentation"),
                H("At most two fresh labels augment every native legal word"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every m>=3,r>=1, put k=m*r and d=(2^k-1)/(2^m-1). Every actual Legal(k,d,W) with G(k,d,W)>0 admits an actual Legal(k,d,V) with J(k,d,V)<J(k,d,W), at most two labels in V.toFinset minus W.toFinset, and only SMALL labels in W.toFinset minus V.toFinset. J is the exact original all-length lexicographic triple (G,H,U). W is arbitrary: no minimizer, competitor, coprimality, injectivity, prefix sign, favorable packet, block placement or arrival gate is assumed.")),
                    Paragraph(Text("In scaled coordinates B=2^(m-2), M=2*B-1. Reset decomposition and the old allocation retain every original label. If the tail is below B, physical occupancy and G>0 force a fresh top label that appends legally. Otherwise any occupied-height bin missing a top supplies an exact-B SMALL subcollection; returning that physical subcollection and inserting a fresh top preserves its endpoint and every other bin. These branches strictly lower G, regardless of a possible increase in U.")),
                    Paragraph(Text("When every old bin has its unique physical top, their total is p=n+1<=r, where n is the number of old resets. A full tail permits a fresh reset. A fresh SMALL coin fitting the gap appends and strictly lowers U while G and H stay fixed. Otherwise the least fresh denomination 2^j exceeds the gap g. Its minimality proves ownership of every lower physical denomination. Original bins give the higher-scale residue bounds. Mass conservation and the complete low budget show p<r, supplying a fresh reset without a gate premise.")),
                    Paragraph(Text("The coupled allocator partitions all old SMALL labels plus the one fresh SMALL label into p bins of capacity B-1 and a tail of capacity 2^j-g. Retained physical top labels head the bins; retained resets and the fresh reset end them. Every complete packet moves 0 to B, increases monotonically to M, then resets to zero. The final tail increases from zero to 2^j-g. No illegal intermediate append is used. The actual permutation retains every old label in this branch and inserts exactly the two selected fresh labels.")),
                    Paragraph(Text("The proof uses physical_balance and mapped permutations for the exact G,H,U balances and strict nested Lex comparison. The existing LARGE-only Inventory is not applied to mixed insertions. The positive source denominations are powers of two, and the native capacity is half(k), not SourceWidth.capacity. Full Circle C3.1 for arbitrary t and signed source interactions remains open; no family completion or global-minimum corollary is delivered.")),
                    Paragraph(Text("The surrounding source problem is Damasdi, Frankl, Pach and Palvolgyi, Monochromatic configurations on a circle, arXiv:2504.10687v2, Conjecture 3.1, DOI 10.5070/C6.68671. The labelled allocation and restricted-family exchange are the repository construction; no literature novelty claim is made."))),
                DescribeRole.Theorem)), []));
}
