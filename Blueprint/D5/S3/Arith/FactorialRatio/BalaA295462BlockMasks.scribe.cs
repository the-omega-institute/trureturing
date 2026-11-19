using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FactorialRatio;

internal sealed class BalaA295462BlockMasksDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FactorialRatio/BalaA295462BlockMasks.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "When a(n) of A295462 is odd, multiplication by n carries every mask below 16 "
            + "blockwise through XOR, AND and OR, and eleven Hanna XOR identities follow.",
        H("Blockwise bit operations for odd A295462 values"),
        Blocks(
            Describe.Lean(DescribeId.Create("bala-a295462-block-masks-result"),
                DeclarationHandle.Create(Prefix + "block_masks"),
                H("Mask blocks and the eleven XOR identities"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let a(n)=(15n)!(2n)!/((10n)!(6n)!n!) be odd. Then for all u,v<16, "
                    + "(un)⊕(vn)=(u⊕v)n, (un)∧(vn)=(u∧v)n and (un)∨(vn)=(u∨v)n bitwise. In "
                    + "particular (un)⊕(vn)=wn for (u,v,w)=(1,14,15), (3,9,10), (3,13,14), "
                    + "(5,9,12), (5,11,14), (6,11,13), (7,9,14), (7,10,13), (7,11,12), "
                    + "(12,21,25) and (12,37,41); these XOR identities were observed by "
                    + "P. D. Hanna (2006) and J. Karlsson (2022). By the parity theorem for "
                    + "A295462, any two occupied binary positions of n differ by at least four. "
                    + "Peeling off the top position 2^e of n=2^e+y gives un=u·2^e+uy with "
                    + "uy<2^e, so the copies of a mask u<16 occupy disjoint four-bit blocks and "
                    + "each bitwise operation acts block by block. For the two larger triples, "
                    + "induct on n: an even n halves, and an odd n is 16m+1 with m again "
                    + "four-separated; then 12n=16(12m)+12, 21n=16(21m+1)+5 and "
                    + "37n=16(37m+2)+5, so the induction proves (12n)⊕(21n+c)=25n+c for "
                    + "c=0,1 and (12n)⊕(37n+c)=41n+c for c=0,1,2 simultaneously."))),
                DescribeRole.Theorem))));
}
