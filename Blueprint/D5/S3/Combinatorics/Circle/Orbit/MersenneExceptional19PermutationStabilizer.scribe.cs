using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.Orbit;

internal sealed class MersenneExceptional19PermutationStabilizerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Selected zero tests determine every physical permutation.",
        H("Selected zero tests determine every physical permutation"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-selected-image-zero-perm-iff"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19PermutationStabilizer.actual_selected_image_zero_perm_iff"),
                H("Exactly 3d-1 selected image-zero tests force identity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural r, including zero, let d=18r+12. If a permutation of the original Fin(3d) labels maps each actual selectedMask to a literal integer-zero subset, it is identity. UpperIndex has cardinality 3d-1. No assumption says the selected masks are invariant or permuted among themselves."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-zero-family-perm-iff"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19PermutationStabilizer.actual_zero_family_perm_iff"),
                H("The full literal zero family has trivial permutation stabilizer"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A permutation preserves zero sums on every literal Finset of the original Fin(3(18r+12)) labels if and only if it is identity. Apply preservation to each selected_literal_zero equation, then the stronger selected-image theorem. Every original subset, label and natural r remains in the telescope."))), DescribeRole.Theorem),
            Paragraph(Text("Direct reconstruction bridge. Put X_i=w_(p i) in Q. Injectivity of the permutation transports each literal image sum to the corresponding selected sum of X. The proved actual_selected_upper_reconstruction gives X_i=primitive_i*c, with c=-3X00+2X20. The exact integer identity w_i=19(B-1)*primitive_i, where B=2^d is at least 4096, yields X_i=lambda*w_i by division only in Q. No arbitrary-group torsion cancellation, rank premise, finite certificate or separate rational-carry annihilator is used.")),
            Paragraph(Text("Permutation and arithmetic meet in the square sum. Every physical weight is nonzero and all weights are distinct, with no opposite pair, by the consumed WeightSeparation arithmetic. Thus S=sum_i w_i^2 is strictly positive. Permutation invariance gives lambda^2*S=S and hence lambda=1 or -1. Injectivity forces p=1 in the positive case; the absence of opposite weights excludes the negative case. This uses the full symmetric-group action on literal zero subsets, beyond cyclic rotations.")),
            Paragraph(Text("Arithmetic source and scope. The WeightSeparation proof follows the supplied direct-carry candidate, adapted to the live Orbit owners. It proves order_Q(2)=3d from Q>(2^(3d/2)+1), and uses an explicit Bezout inverse for a modulo Q. The selected reconstruction and integer basis are reused unchanged. This result addresses permutation rigidity; it makes no unrestricted four-gap J or official whole-repository admission claim."))), []));
}
