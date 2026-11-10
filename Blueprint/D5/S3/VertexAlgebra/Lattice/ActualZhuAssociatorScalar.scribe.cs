using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class ActualZhuAssociatorScalarDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed binomial kernels used on the live derivation path of the actual Zhu associator.",
        H("The two associator kernels"),
        Blocks(
            Paragraph(Text("The private U kernel sums, for 0 <= i <= b+1, the product "
                + "(-1)^i C(m+i,i) C(K,m+1+i) C(K+L-m-1-i,b+1-i). "
                + "It equals the sum of C(K,m+1+j) C(L,b+1-j) over 0 <= j <= b+1. "
                + "Here K,L,b are natural, m is any integer, and C(r,s) is zero for negative s "
                + "and otherwise the existing integerBinomial(r,s.toNat).")),
            Paragraph(Text("The private V kernel sums, for 0 <= a <= K, "
                + "C(K,a) C(K+L-a,g+2+d-a) (-1)^d C(a-1,d) [-(-1)^(a-1)]. "
                + "It equals the sum of C(L,g+2+k) C(K,d-k) over 0 <= k <= d. "
                + "K,L,d are natural and g is any integer. The a=0 term uses the integer upper "
                + "index -1 and integer exponent -1; no truncated natural subtraction is used.")),
            Paragraph(Text("The proof ports Fedor K. Popov's Apache-2.0 ZhuUCore.lean and ZhuVCore.lean "
                + "from Fedor-Popov/Lean_VOA revision 013a799ca834a8a6b3afa8129e3e522025b3f45c. "
                + "The immutable source SHA256 values are "
                + "91a719766953e94b3b7c227dff738b8e52639c76b5fead2a645c158ab6d61198 and "
                + "1c678f98391c0a8e6b921bccb23b823fb9d10785a7fa787478044437d806fb3c. "
                + "Native Ring.choose_neg supplies upper negation; the existing ActualZhuBinomial "
                + "owner supplies signed binomials, Vandermonde, and trinomial revision. "
                + "Upstream uses Lean v4.30.0 and mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f; "
                + "this native port uses Lean v4.35.0 and mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679. "
                + "This is literature-attested, with no claim of independent mathematical novelty. "
                + "The classical source is Zhu's associativity argument, also developed by Frenkel and Zhu.")),
            Paragraph(Text("The unfinished typed audit of the public associator and mu_identity consumers is "
                + "https://github.com/the-omega-institute/trureturing/issues/28745. It requires faithful full-telescope "
                + "reconstruction and equivalence, a lawful enrolled-template readout and actual-positive law, "
                + "whole-family intervention and sensitivity, and actual observational dependence, preserving constant "
                + "and degenerate fibres. These private kernels supply no declared_validated registration.")),
            Paragraph(Text("These are private consumed helpers. ActualZhuAssociator uses both kernels "
                + "to identify its two state-field iterate families with finite higher-circle towers. "
                + "The scalar identities alone make no assertion about a quotient ring or a physical CFT.")))));
}
