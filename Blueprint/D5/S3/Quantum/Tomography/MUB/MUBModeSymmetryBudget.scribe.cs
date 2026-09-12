using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography.MUB;

internal sealed class MUBModeSymmetryBudgetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three-mode collision, mixing, and centered-square coordinates obey exact budgets.",
        H("MUB Mode Symmetry Budget"),
        Blocks(
            Describe.Lean(
                DescribeId.Create(
                    "mode-budget-three-mode-collision-coordinate"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget."
                    + "threeModeCollision"),
                H("Three-mode collision coordinate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a real triple p, the collision coordinate is the sum of the "
                    + "squares of its three entries."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create(
                    "mode-budget-three-mode-mixing-coordinate"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget."
                    + "threeModeMixing"),
                H("Three-mode mixing coordinate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a real triple p, mixing is one minus its collision coordinate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create(
                    "mode-budget-displacement-from-uniform-weights"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget."
                    + "threeModeCenteredSquare"),
                H("Displacement from uniform weights"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a real triple p, the centered square is the sum of the squared "
                    + "differences between its entries and one-third."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create(
                    "mode-budget-mixing-from-pair-products"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget."
                    + "threeModeMixing_eq_pairProducts"),
                H("Mixing from pair products"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If a real triple sums to one, its mixing equals twice the sum of its "
                    + "three distinct pair products."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "mode-budget-nonnegative-probability-mixing"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget."
                    + "threeModeMixing_nonneg"),
                H("Nonnegative probability mixing"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A nonnegative real triple whose entries sum to one has nonnegative "
                    + "mixing."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "mode-budget-collision-lower-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget."
                    + "one_third_le_threeModeCollision"),
                H("Collision lower bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Any real triple whose entries sum to one has collision at least "
                    + "one-third."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "mode-budget-mixing-upper-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget."
                    + "threeModeMixing_le_two_thirds"),
                H("Mixing upper bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Any real triple whose entries sum to one has mixing at most "
                    + "two-thirds."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "mode-budget-centered-collision-excess"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget."
                    + "threeModeCenteredSquare_eq_collision_sub_one_third"),
                H("Centered collision excess"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any real triple whose entries sum to one, its centered square "
                    + "equals its collision minus one-third."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "mode-budget-equality-characterizes-uniform-weights"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget."
                    + "threeModeMixing_eq_two_thirds_iff"),
                H("Equality characterizes uniform weights"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any real triple whose entries sum to one, mixing equals two-thirds "
                    + "if and only if each entry is one-third."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "mode-budget-collision-across-six-rows"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget."
                    + "modeCollisionTotal"),
                H("Collision across six rows"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For six real triples, total collision is the sum of their three-mode "
                    + "collision coordinates."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create(
                    "mode-budget-mixing-across-six-rows"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget."
                    + "modeMixingTotal"),
                H("Mixing across six rows"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For six real triples, total mixing is the sum of their three-mode "
                    + "mixing coordinates."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create(
                    "mode-budget-centered-squares-across-six-rows"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget."
                    + "modeCenteredSquareTotal"),
                H("Centered squares across six rows"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For six real triples, the total centered square is the sum of their "
                    + "squared displacements from uniform three-mode weights."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create(
                    "mode-budget-algebraic-affinity-coordinate"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget."
                    + "modeAffinityTotal"),
                H("Algebraic affinity coordinate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For six real triples, affinity is total collision minus two, divided "
                    + "by two. This is an algebraic coordinate; identifying it with chordal "
                    + "subspace affinity requires the projector-plane bridge."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create(
                    "mode-budget-total-mixing-and-collision-identity"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget."
                    + "modeMixingTotal_eq_six_sub_collision"),
                H("Total mixing and collision identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any six real triples, total mixing equals six minus total "
                    + "collision."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "mode-budget-six-row-centered-collision-excess"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget."
                    + "modeCenteredSquareTotal_eq_collision_sub_two"),
                H("Six-row centered collision excess"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If each of six real triples sums to one, the total centered square "
                    + "equals total collision minus two."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "mode-budget-affinity-as-half-the-centered-square"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget."
                    + "modeAffinityTotal_eq_half_centeredSquare"),
                H("Affinity as half the centered square"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If each of six real triples sums to one, affinity equals one-half of "
                    + "the total centered square."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "mode-budget-mixing-and-affinity-identity"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget."
                    + "modeMixingTotal_eq_four_sub_two_mul_affinity"),
                H("Mixing and affinity identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any six real triples, total mixing equals four minus twice the "
                    + "affinity coordinate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "mode-budget-total-probability-mixing-interval"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/MUBModeSymmetryBudget."
                    + "modeMixingTotal_mem_Icc"),
                H("Total probability mixing interval"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For six nonnegative real triples each summing to one, total mixing "
                    + "lies in the closed interval from zero to four."))),
                DescribeRole.Theorem))));
}
