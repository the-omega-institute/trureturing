using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.Adjacent;

internal sealed class FourNegativeAdjacentDoubleJointLiftDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Private centered-chain identities for the adjacent paired-gap branch r=s+1",
        H("The four old and new physical chains"),
        Blocks(
            Paragraph(Text("This module supplies private support proofs, shift and chains, for the public actualSource_four_negative_adjacent_double_joint_lift theorem in FourNegativeAdjacentDoublePhysical. Let n=s>=2, r=n+1, z=2^n, k=2(n+1)+2n and N=2^k-1=4z^4-1. Put A=4z^3+4z^2+2z+1, B=4z^3+2z^2+z+1, L=2z^3+z^2+z+1 and M=2z^3+2z^2+2z+1. The old and new increments are f(i)=centered(N,2^i A) and g(i)=centered(2N+1,2^i(2A)).")),
            Paragraph(Text("The exact old identities are zA=N+B, zB=N+L, 2zL=N+M and 2zM=N+A. Write GU=2A, GV=2B-1, GW=2L-1-z and GX=2M-1-2z-2z^2. Their new counterparts are zGU=(2N+1)+GV, zGV=(2N+1)+GW, 2zGW=(2N+1)+GX and 2zGX=(2N+1)+A. The shift proof transfers each identity to all subsequent doubled powers modulo its modulus; the existing centered_ladder proof determines the centered representatives.")),
            Paragraph(Text("The physical chains have labels U_i=i and V_i=n+i for 0<=i<n, and W_i=2n+i and X_i=3n+1+i for 0<=i<n+1. Except at the last position of each chain, their old values are respectively 2^i A, 2^i B, 2^i L and 2^i M. The last old values are respectively -(N-B)/2, -(N-L)/2, -(N-M)/2 and -(N-A)/2. In the same physical positions the new positive coefficients are GU, GV, GW and GX, and the last values are respectively -((2N+1)-GV)/2, -((2N+1)-GW)/2, -((2N+1)-GX)/2 and -((2N+1)-A)/2. These halves are exact integers. The fresh physical label k has new value g(k)=A.")),
            Paragraph(Text("FourNegativeAdjacentDoublePhysical consumes chains to establish its positive blocks, negative jumps, block masses and fresh-ear value. FourNegativeAdjacentDoubleSchedule supplies the complementary inventory and strip inequalities used with these identities. The labels remain physical occurrences even when their numerical values coincide; no coprimality or primitive-period hypothesis is imposed.")),
            Paragraph(Text("These identities support only the paired branch r=s+1 with s>=2. They do not establish unrestricted r,s, the full physical J endpoint or Circle Conjecture 3.1. The unrestricted J problem remains open."))), []));
}
