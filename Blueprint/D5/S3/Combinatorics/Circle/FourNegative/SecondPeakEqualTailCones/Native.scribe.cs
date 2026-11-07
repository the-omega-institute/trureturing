using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones;
internal sealed class NativeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native masks for the two upper cones", H("Safe natural arithmetic before physical allocation"),
        Blocks(
            Paragraph(Text("Assume s>=2 and either 2s+2<=a with a+1<=b, or s+1<=a with max(a+1,3s+1)<=b. These premises imply a>=s+1, b>=a+1 and b>=2s. With x=2^a,y=2^b,z=2^s, set lambda=2^(b-a-1), epsilon=0 for b=a+1 and epsilon=2^(b-a-2) otherwise. The W allocation is p=y/(2z)+y/z^2-1-epsilon. Its nested capacities are H=2^(b-s)-1 and F=2^(b-1)-1.")),
            Paragraph(Text("The adaptive X allocation is C=2^(a-s-1)-delta, where delta=1 when b>=3s+1 and delta=0 otherwise; its capacity is E=2^(a-1)-1. Exact power factorizations justify the natural quotients and integer casts, including every subtraction. The bounds are 0<=p<=H<=F and 0<=C<=E. Only the capacities H,F,E are required to be all-ones masks: C may be an arbitrary submask of E when delta=0, and C=0 is allowed.")),
            Paragraph(Text("The bitwise complement identities become H XOR p=H-p, F XOR H=F-H and E XOR C=E-C, with safe integer casts. The low-bit bound ensures every decoded set bit is a legal local positive position. These facts support a partition of physical occurrences, without replacing the masks by merely equal numerical masses."))), []));
}
