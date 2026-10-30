using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Incidence;

internal sealed class UnsignedStarFixedCokernelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Incidence/UnsignedStarFixedCokernel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral fixed representatives and the canonical fixed unsigned-star cokernel comparison on original indexed coordinates.",
        H("Integral Fixed Unsigned-Star Cokernels"),
        Blocks(
            Describe.Lean(DescribeId.Create("star-equivariance"),
                DeclarationHandle.Create(Prefix + "starMap_equivariant"), H("Equivariance of the Original Integer Star Map"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing equivariance proof is exposed unchanged for invariant-support consumers. Independent endpoint swaps remain allowed; no fixed-cokernel lifting or comparison theorem is assumed by those consumers."))), DescribeRole.Theorem),
            Paragraph(Text("V and X are the finite original vertex and edge-ID types. "
                + "The original graph is connected, nonbipartite and loopless, and parallel original edge IDs remain separate. "
                + "An arbitrary group Gamma acts by vertexPerm and edgePerm, homomorphisms to the two permutation groups. "
                + "The endpoints condition permits an independent orientation swap at each group element and edge ID. "
                + "The action on integer coordinates is (gamma.a)(v)=a(vertexPerm(gamma)^(-1)(v)), and similarly on X. "
                + "The integer star map is exactly F(a)(i)=a(left(i))+a(right(i)).")),
            Describe.Lean(DescribeId.Create("integral-fixed-representative"),
                DeclarationHandle.Create(Prefix + "exists_fixed_representative"),
                H("A Fixed Integral Representative of Every Fixed Class"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every fixed class x of the actual quotient "
                    + "Z^X/F(Z^V) has an integer vector y fixed on the original X coordinates with quotient class x. "
                    + "Gamma need not be finite. The consumed supplier corollary starMap_injective reuses the existing "
                    + "private nonbipartite_potential proof over Z. Each actual difference gamma.z-z has a unique integer "
                    + "F-potential c(gamma), and injectivity proves the cocycle equation on the original arbitrary group. "
                    + "The differences factor through permutations of the ORIGINAL finite edge-ID type X. F-injectivity "
                    + "therefore makes the vector range of c finite, so every coordinate range is finite. An attained "
                    + "integer maximum d(v) of each actual coordinate range and the cocycle identity give c(gamma)=d-gamma.d "
                    + "with actual integer d. Then y=z+F(d) is fixed and represents x. No integral average or divisibility "
                    + "of the group order is assumed, and no cocycle correction is an extra premise."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("canonical-fixed-cokernel-comparison"),
                DeclarationHandle.Create(Prefix + "fixedCokernelEquiv"),
                H("The Canonical Integral Comparison"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("fixedStarMap restricts the original F to the fixed vertex and edge submodules. "
                + "fixedProjection restricts the original quotient projection. If a fixed edge vector equals F(a), "
                + "injectivity of F forces a to be fixed. Its kernel is therefore exactly F((Z^V)^Gamma). "
                + "fixedCokernelEquiv uses this kernel identity, fixed-representative surjectivity and Mathlib's first "
                + "isomorphism theorem to construct the canonical natural integral linear equivalence "
                + "(Z^X)^Gamma/F((Z^V)^Gamma) ~= (Z^X/F(Z^V))^Gamma. Its forward map is induced by the original "
                + "quotient projection. A chosen representative or correction is not canonical; no splitting of the "
                + "whole cokernel is asserted, and no support bound or bipartite generalization is claimed. For every fixed integer y, the forward map sends its class to the original quotient class mkQ(y)."))),
                DescribeRole.Definition),
            Paragraph(Text("Attribution: approved native source P1/P6, SHA256 "
                + "ed356c4b82a313d22d45def66d4fa89932c0fa9bb212867b5a25bb3f503cca81. "
                + "The private correction adapts the separate UNCOMPILED PermutationCocycleFiniteRange.lean, SHA256 "
                + "a9994bfa430250c44505ba80c3e35d286edb0823f2a707e84209712ba55f1a5f, using attained coordinate maxima. "
                + "It supplies proposed source, not independent review or kernel evidence. Existing connected potential "
                + "arithmetic is reused from UnsignedStarTorsion, originally attributed "
                + "there to the caller's Sections 6-7, SHA256 f776b4a6cba72126daf67658b7c846279a39d61cbdd41f6e2cfdd400f8e487f8. "
                + "The minimal supplier patch adds only its consumed integer injectivity corollary and preserves that private proof. Native approval is mathematical guidance, "
                + "not kernel or publication evidence. No literature-priority claim is made.")))));
}
