using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.Orbifold;

internal sealed class IsingVacuumPairingDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/VertexAlgebra/TwistedGround/Orbifold/IsingVacuumPairing.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original Ising mode-three vacuum channels",
        H("The original Ising mode-three vacuum channels"),
        Blocks(
            Paragraph(Text("The input space is the whole negative twisted carrier at physical "
                + "energy two for a rank-24 lattice with unit Gram determinant. The axis is "
                + "the actual fixed state of a charge of norm four with sign s satisfying s² = 1. "
                + "These hypotheses include both signs in each of the 24 Leech frame directions.")),
            Describe.Lean(DescribeId.Create("ising-grade-two-positive-modes"),
                DeclarationHandle.Create(Owner + "oddAxisMode_pos_eq_zero_energyTwo"),
                H("Positive modes on physical energy two"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every positive integer Ising mode kills this full grade. "
                    + "The source has energy two and the raw doubled index for axis mode k is "
                    + "−2(k+1)−2. The corresponding signed oscillator output grade is 1−2k."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ising-actual-mode-three-pairing"),
                DeclarationHandle.Create(Owner + "originalI_three_energyTwo"),
                H("The mode-three pairing"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive real Gram, the original two-twisted mode "
                    + "three on physical energy-two inputs u and v is the fixed vacuum times "
                    + "the ordered scalar actualForm(v,u). The original inverse of the source "
                    + "pairing realizes the output on grade zero."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ising-vacuum-off-diagonal"),
                DeclarationHandle.Create(Owner + "originalI_three_offDiagonal"),
                H("Vanishing for distinct axis weights"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For unequal axis weights among 0, 1/2 and 1/16, the "
                    + "actual mode-three product is zero. The fixed lattice pairing with "
                    + "the vacuum is a dual primary of weight zero. On a fixed input of "
                    + "grade n, the axis mode k changes the grade to n−k. For k ≤ 0, only "
                    + "n = k = 0 can contribute to the vacuum pairing, and creation kills "
                    + "that term. The original primary selection law forces equality of "
                    + "the two input weights whenever the vacuum coefficient is nonzero."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ising-vacuum-pairing-nondegenerate"),
                DeclarationHandle.Create(Owner + "vacuumPairing_nondegenerate"),
                H("Nondegeneracy in each axis eigenspace"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The ordered pairing has zero left and right radicals "
                    + "on each of the three literal axis eigenspaces. Ambient nondegeneracy "
                    + "and orthogonality of different oscillator grades first give zero "
                    + "radical on the full physical grade. The three actual grade-one "
                    + "projectors decompose every test vector. The unequal-weight "
                    + "pairings vanish, so a block radical vector is in the full radical."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ising-assembled-vacuum-partner"),
                DeclarationHandle.Create(Owner + "exists_sameWeight_vacuum_partner"),
                H("A normalized partner in the same eigenspace"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each nonzero input, nondegeneracy supplies a partner "
                    + "of the same weight with a nonzero ordered pairing. Scaling that partner "
                    + "by the inverse pairing gives the actual fixed vacuum under mode three "
                    + "of the assembled orbifold field."))),
                DescribeRole.Theorem))));
}
