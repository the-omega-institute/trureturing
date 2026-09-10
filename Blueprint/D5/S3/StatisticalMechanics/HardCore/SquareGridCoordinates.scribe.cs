using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.HardCore;

internal sealed class SquareGridCoordinatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact correspondence between grid geometry and actual independent-set messages.",
        H("SquareGridCoordinates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hc-squaregridcoordinates-squaregrid"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.squareGrid"),
                H("The actual infinite square grid"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All four nearest-neighbor edges are defined on the previously owned integer-pair coordinate carrier."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hc-squaregridcoordinates-shiftto"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.shiftTo"),
                H("Center an arbitrary root"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The explicit inverse adds the root coordinates back."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hc-squaregridcoordinates-recenterequiv"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.recenterEquiv"),
                H("The actual recenter map is bijective"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The forward map is the existing OrderedGridMemory.recenter. The inverse undoes the translation and quarter-turn."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hc-squaregridcoordinates-shift-adj-iff"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.shift_adj_iff"),
                H("Translations preserve and reflect adjacency"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This checks the actual coordinate formulas rather than assuming a graph automorphism."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hc-squaregridcoordinates-recenter-adj-iff"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.recenter_adj_iff"),
                H("Recentered edges are exactly grid edges"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All three maps preserve and reflect the nearest-neighbor relation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hc-squaregridcoordinates-recenter-direction"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.recenter_direction"),
                H("The selected neighbor becomes the origin"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This fixes the marked vertex in the transported child ratio."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hc-squaregridcoordinates-gridpartition"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.gridPartition"),
                H("Actual grid partition sums"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This is an abbreviation for the existing independent-configuration sum at constant activity."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hc-squaregridcoordinates-gridvacancy"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.gridVacancy"),
                H("Actual marked ratios over a field"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Numerator and denominator are actual grid partitions. Division is total as a field operation; legitimate recursive cancellation requires separately proved nonzero denominators."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hc-squaregridcoordinates-partition-recenter"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.partition_recenter"),
                H("Exact partition invariance"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The general configuration-bijection theorem is applied to the actual grid map. The conclusion holds in every commutative semiring."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hc-squaregridcoordinates-vacancy-recenter"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.vacancy_recenter"),
                H("Exact marked-ratio invariance"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both numerator and denominator transport. Equality at zero denominators is an equality of total field expressions, not a claim of analytic regularity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hc-squaregridcoordinates-vacancy-shift"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.vacancy_shift"),
                H("Every marked root can be centered"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The theorem concerns constant activities. General inhomogeneous weights are covered only by the explicit pullback in PartitionRelabeling."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hc-squaregridcoordinates-before-child-subset-erase"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.before_child_subset_erase"),
                H("The old root is removed before every child"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The prescribed deletion always includes the current origin."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hc-squaregridcoordinates-advance-card-lt"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/SquareGridCoordinates.advance_card_lt"),
                H("Every child is strictly smaller"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Image cardinality and actual root deletion give the well-founded measure needed for the subsequent nonvanishing induction."))),
                DescribeRole.Theorem))));
}
