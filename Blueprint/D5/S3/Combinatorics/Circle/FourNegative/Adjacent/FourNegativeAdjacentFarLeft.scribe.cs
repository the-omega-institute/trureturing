using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.Adjacent;

internal sealed class FourNegativeAdjacentFarLeftDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Low and high masks on the same physical X chain",
        H("Exact physical construction and coupled prefix strips"),
        Blocks(
            Paragraph(Text("Take independent r,s>=2 with r>=s+2, d=r-s, n=r-2s in natural subtraction, x=2^r,y=2^s,T=2^d and p=2^n. The positive X indices split into the low interval of length d and the high interval of length s-1. Within the low interval, the one position n gives mass pM; erasing this occurrence leaves mass (T-p-1)M. The high interval has mass (x/2-T)M. These are physical positions, including when numerical source values repeat.")),
            Paragraph(Text("The old order is W-positive,W-negative,X-singleton,U-positive,U-negative,X-high,X-negative,X-low-rest,V-positive,V-negative. The ear is inserted immediately before X-negative at the exact cut r+2s. Range concatenation and perm_cons_erase establish the inventory. The private small_arithmetic and large_arithmetic proofs cover r<=2s and r>2s. They put respectively x=4cb,y=2b with c>=2,b>=c, and x=4pb^2,y=2b with p>=1,b>=2. Exact integer half-jumps are normalized before shifting to nonnegative variables; all seam and peak margins become polynomials with nonnegative coefficients.")),
            Paragraph(Text("The uniform centered table comes from FourNegativeAdjacentSource. The four-strip consumer converts these exact masses and jumps into every natural old and new prefix, then marked_word and lift_order transport the original labels to Fin k and Fin(k+1). Both complete sums are checked through source_zero. The construction preserves the physical occurrence at each index and requires neither a unit gcd nor a minimal numerical period."))), []));
}
