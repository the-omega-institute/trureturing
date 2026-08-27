using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.ExperimentCost;

internal sealed class KernelTowerNilpotentRecoveryDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Estimation/ExperimentCost/KernelTowerNilpotentRecovery.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kernel dimensions recover positive nilpotent block profiles and separate the "
            + "characteristic-polynomial residual.",
        H("Kernel Towers Recover Nilpotent Block Profiles"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("positive-block-size"),
                Handle("PositiveBlockSize"),
                H("Positive block size"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A block size is a natural number equipped with a proof that it is "
                        + "positive."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("block-multiset"),
                Handle("BlockMultiset"),
                H("Block multiset"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An unordered finite multiset records the positive block sizes."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("block-profile-dimension"),
                Handle("blockProfileDimension"),
                H("Block-profile dimension"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The represented ambient dimension is the sum of all block sizes."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nilpotent-block-profile"),
                Handle("NilpotentBlockProfile"),
                H("Nilpotent block profile"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An n-dimensional profile is a block multiset whose sizes sum to n."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("block-kernel-tower"),
                Handle("blockKernelTower"),
                H("Abstract kernel-dimension tower"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At step k, each block of size s contributes the minimum of k and s."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("kernel-increment"),
                Handle("kernelIncrement"),
                H("Kernel-tower increment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The named increment is the natural-number difference a_k - a_(k-1)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("block-count-at-least"),
                Handle("blockCountAtLeast"),
                H("Blocks at least a given size"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This count selects blocks whose positive size is at least k."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("block-count-exactly"),
                Handle("blockCountExactly"),
                H("Blocks of an exact size"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This count selects blocks whose positive size is exactly k."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("matrix-kernel-dimension-tower"),
                Handle("matrixKernelDimensionTower"),
                H("Matrix kernel-dimension tower"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For an actual matrix N, the kth value is the dimension of ker(N^k)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("unit-block-size"),
                Handle("unitBlockSize"),
                H("Unit block size"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The distinguished positive size one represents a one-by-one block."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zero-matrix-block-profile"),
                Handle("zeroMatrixBlockProfile"),
                H("Zero-matrix block profile"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The n-dimensional zero matrix has n blocks, all of size one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("single-nilpotent-block-profile"),
                Handle("singleNilpotentBlockProfile"),
                H("Single nilpotent block profile"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A singleton profile packages one positive nilpotent block."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("kernel-increment-counts-blocks-at-least"),
                Handle("kernel_increment_counts_blocks_at_least"),
                H("Kernel increments count surviving blocks"),
                StatementSource.FromAuthor(IncrementCountFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At every positive index k + 1, the tower increment equals the number "
                        + "of blocks whose size is at least k + 1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exact-block-count-from-successive-increments"),
                Handle("exact_block_count_from_successive_increments"),
                H("Successive increments give exact block counts"),
                StatementSource.FromAuthor(ExactCountFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The number of blocks of size exactly k is b_k minus b_(k+1), "
                        + "including the zero-index boundary."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-kernel-tower-recovers-block-profile"),
                Handle("finite_kernel_tower_recovers_block_profile"),
                H("The finite tower recovers the block profile"),
                StatementSource.FromAuthor(FiniteRecoveryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two n-dimensional positive block profiles with equal tower values from "
                        + "one through n are equal as multisets."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("matrix-kernel-tower-stabilizes-at-dimension"),
                Handle("matrix_kernel_tower_stabilizes_at_dimension"),
                H("Matrix kernel towers stabilize by dimension"),
                StatementSource.FromAuthor(StabilizationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every n-dimensional matrix and k at least n, ker(N^k) and ker(N^n) "
                        + "have equal dimensions. Nilpotence is not required."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-matrix-block-profile-audit"),
                Handle("zero_matrix_block_profile_audit"),
                H("Zero-matrix profile audit"),
                StatementSource.FromAuthor(ZeroMatrixAuditFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The n unit blocks give a_k = n for positive k, b_1 = n, and b_k = 0 "
                        + "from step two onward."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("single-nilpotent-block-profile-audit"),
                Handle("single_nilpotent_block_profile_audit"),
                H("Single-block profile audit"),
                StatementSource.FromAuthor(SingleBlockAuditFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "One block of size s has a_k = min(k,s), with the expected indicator "
                        + "counts for at-least and exact sizes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-dimensional-block-profile-audit"),
                Handle("zero_dimensional_block_profile_audit"),
                H("Zero-dimensional profile audit"),
                StatementSource.FromAuthor(ZeroDimensionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A zero-dimensional positive profile is empty and every tower value is "
                        + "zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("one-dimensional-block-profile-audit"),
                Handle("one_dimensional_block_profile_audit"),
                H("One-dimensional profile audit"),
                StatementSource.FromAuthor(OneDimensionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every one-dimensional positive profile is the singleton unit-block "
                        + "profile of the zero matrix."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-index-is-necessary"),
                Handle("positive_index_is_necessary"),
                H("The positive-index condition is necessary"),
                StatementSource.FromAuthor(PositiveIndexFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For one unit block, b_0 is zero while one block has size at least zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kernel-tower-equality-is-necessary"),
                Handle("kernel_tower_equality_is_necessary"),
                H("Tower equality is necessary for recovery"),
                StatementSource.FromAuthor(TowerEqualityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In dimension two, one size-two block and two size-one blocks are distinct "
                        + "and already have different first tower values."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kernel-tower-separates-charpoly-residual"),
                Handle("kernel_tower_separates_charpoly_residual"),
                H("The kernel tower separates the characteristic-polynomial residual"),
                StatementSource.FromAuthor(ResidualSeparationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "FPOD 188.1's zero and square-zero matrices have equal characteristic "
                        + "polynomials and are not conjugate, but their first nullities are "
                        + "two and one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("dimension-bound-is-necessary"),
                Handle("dimension_bound_is_necessary"),
                H("The stabilization bound cannot be removed"),
                StatementSource.FromAuthor(DimensionBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A two-dimensional square-zero rational matrix has first nullity one and "
                        + "second nullity two."))),
                DescribeRole.Theorem))));

    private static Formula IncrementCountFormula()
    {
        Formula blocks = F.Id("B");
        Formula k = F.Id("k");
        Formula step = Seq(k, Plus, D(1));
        return Disp(Seq(
            Forall, Sp, blocks, Comma, Sp, k, Comma, Sp,
            Call("kernelIncrement", blocks, step), Sp, Eq, Sp,
            Call("blockCountAtLeast", blocks, step), Dot));
    }

    private static Formula ExactCountFormula()
    {
        Formula blocks = F.Id("B");
        Formula k = F.Id("k");
        return Disp(Seq(
            Forall, Sp, blocks, Comma, Sp, k, Comma, Sp,
            Call("blockCountExactly", blocks, k), Sp, Eq, Sp,
            Call("kernelIncrement", blocks, k), Sp, Minus, Sp,
            Call("kernelIncrement", blocks, Seq(k, Plus, D(1))), Dot));
    }

    private static Formula FiniteRecoveryFormula()
    {
        Formula n = F.Id("n");
        Formula left = F.Id("B");
        Formula right = F.Id("C");
        Formula k = F.Id("k");
        Formula towerClause = Seq(
            Forall, Sp, k, Comma, Sp, D(1), Sp, Leq, Sp, k, Sp, Leq, Sp, n,
            Sp, Rightarrow, Sp, Call("a", left, k), Sp, Eq, Sp, Call("a", right, k));
        return Disp(Seq(
            Forall, Sp, n, Comma, Sp, left, Comma, Sp, right, Colon, Sp,
            Call("NilpotentBlockProfile", n), Comma, RowBreak, Grp(),
            Grp(towerClause), Sp, Rightarrow, Sp, left, Sp, Eq, Sp, right, Dot));
    }

    private static Formula StabilizationFormula()
    {
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula matrix = F.Id("N");
        return Disp(Seq(
            Forall, Sp, matrix, Colon, Sp, Call("Matrix", n), Comma, Sp, k, Comma, Sp,
            n, Sp, Leq, Sp, k, Sp, Rightarrow, Sp,
            Call("matrixKernelDimensionTower", matrix, k), Sp, Eq, Sp,
            Call("matrixKernelDimensionTower", matrix, n), Dot));
    }

    private static Formula ZeroMatrixAuditFormula()
    {
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula profile = Call("zeroMatrixBlockProfile", n);
        return Disp(Seq(
            Call("blockCountExactly", profile, D(1)), Sp, Eq, Sp, n, Sp, Land, RowBreak,
            Grp(Forall, Sp, k, Sp, Gt, Sp, D(0), Comma, Sp,
                Call("a", profile, k), Sp, Eq, Sp, n), Sp, Land, RowBreak,
            Call("b", profile, D(1)), Sp, Eq, Sp, n, Sp, Land, Sp,
            Grp(Forall, Sp, k, Sp, Geq, Sp, D(2), Comma, Sp,
                Call("b", profile, k), Sp, Eq, Sp, D(0)), Dot));
    }

    private static Formula SingleBlockAuditFormula()
    {
        Formula size = F.Id("s");
        Formula k = F.Id("k");
        Formula profile = Call("singleNilpotentBlockProfile", size);
        return Disp(Seq(
            Forall, Sp, size, Sp, Gt, Sp, D(0), Comma, Sp, k, Comma, RowBreak, Grp(),
            Call("a", profile, k), Sp, Eq, Sp, Call("min", k, size), Sp, Land, Sp,
            Call("blockCountAtLeast", profile, k), Sp, Eq, Sp,
            Call("indicator", Seq(k, Sp, Leq, Sp, size)), Sp, Land, RowBreak, Grp(),
            Call("blockCountExactly", profile, k), Sp, Eq, Sp,
            Call("indicator", Seq(size, Sp, Eq, Sp, k)), Dot));
    }

    private static Formula ZeroDimensionFormula() =>
        Disp(Seq(
            Forall, Sp, F.Id("B"), Colon, Sp, Call("NilpotentBlockProfile", D(0)),
            Comma, Sp, F.Id("B"), Sp, Eq, Sp, F.Id("empty"), Sp, Land, Sp,
            Grp(Forall, Sp, F.Id("k"), Comma, Sp,
                Call("a", F.Id("B"), F.Id("k")), Sp, Eq, Sp, D(0)), Dot));

    private static Formula OneDimensionFormula() =>
        Disp(Seq(
            Forall, Sp, F.Id("B"), Colon, Sp, Call("NilpotentBlockProfile", D(1)),
            Comma, Sp, F.Id("B"), Sp, Eq, Sp,
            Call("zeroMatrixBlockProfile", D(1)), Dot));

    private static Formula PositiveIndexFormula() =>
        Disp(Seq(
            Call("kernelIncrement", F.Id("unitProfile"), D(0)), Sp, Neq, Sp,
            Call("blockCountAtLeast", F.Id("unitProfile"), D(0)), Dot));

    private static Formula TowerEqualityFormula()
    {
        Formula left = F.Id("B");
        Formula right = F.Id("C");
        return Disp(Seq(
            Exists, Sp, left, Comma, Sp, right, Colon, Sp,
            Call("NilpotentBlockProfile", D(2)), Comma, Sp,
            left, Sp, Neq, Sp, right, Sp, Land, Sp,
            Call("a", left, D(1)), Sp, Neq, Sp, Call("a", right, D(1)), Dot));
    }

    private static Formula ResidualSeparationFormula()
    {
        Formula zero = F.Id("A");
        Formula nilpotent = F.Id("N");
        return Disp(Seq(
            Call("charpoly", zero), Sp, Eq, Sp, Call("charpoly", nilpotent),
            Sp, Land, Sp, Call("IsNilpotent", zero), Sp, Land, Sp,
            Call("IsNilpotent", nilpotent), Sp, Land, Sp,
            Neg, Call("Conjugate", zero, nilpotent), Sp, Land, RowBreak, Grp(),
            Call("a", zero, D(1)), Sp, Eq, Sp, D(2), Sp, Land, Sp,
            Call("a", nilpotent, D(1)), Sp, Eq, Sp, D(1), Sp, Land, Sp,
            Call("a", nilpotent, D(2)), Sp, Eq, Sp, D(2), Dot));
    }

    private static Formula DimensionBoundFormula() =>
        Disp(Seq(
            Exists, Sp, F.Id("N"), Colon, Sp, Call("Matrix", D(2)), Comma, Sp,
            Call("matrixKernelDimensionTower", F.Id("N"), D(1)), Sp, Neq, Sp,
            Call("matrixKernelDimensionTower", F.Id("N"), D(2)), Dot));

    private static DeclarationHandle Handle(string name) =>
        DeclarationHandle.Create(Prefix + name);
}
