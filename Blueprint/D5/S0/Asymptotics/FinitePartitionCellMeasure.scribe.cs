using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics;

internal sealed class FinitePartitionCellMeasureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonempty finite measurable partition of a probability space has a cell whose measure is at least the uniform share.",
        H("Finite Partition Cell Measure"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a-finite-partition-has-a-cell-of-at-least-uniform-measure"),
                DeclarationHandle.Create(
                    "D5/S0/Asymptotics/FinitePartitionCellMeasure.exists_cell_measure_ge_reciprocal"),
                H("A finite partition has a cell of at least uniform measure"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("mu"), Comma, Sp, F.Id("cell"), Comma, Esc,
                    Operatorname, Grp(F.Id("ProbabilityMeasure")), Open, F.Id("mu"), Close, Comma, Sp,
                    Operatorname, Grp(F.Id("FiniteMeasurablePartition")), Open,
                    F.Id("cell"), Close, Comma, Esc,
                    Exists, Sp, F.Id("i"), Comma, Sp,
                    F.Id("mu"), Open, F.Id("cell"), Open, F.Id("i"), Close, Close,
                    Ge, Sp, F.Id("reciprocal"), Open, F.Id("card"), Open,
                    F.Id("I"), Close, Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite nonempty index type, let the measurable cells be pairwise "
                        + "disjoint and cover the whole carrier. Under a probability measure, at "
                        + "least one cell has measure no smaller than the reciprocal of the number "
                        + "of cells.")),
                    Paragraph(Text(
                        "Mathlib's measure_iUnion identifies the total cell measure with one, and "
                        + "ENNReal.exists_le_of_sum_le supplies the finite averaging step. The Lean "
                        + "declaration only composes these library results.")),
                    Paragraph(Text(
                        "This is a partial closure of the finite-codebook partition clause of source "
                        + "theorem 9.1. The construction of a naming system, countability and height "
                        + "claims, partial decoding, uncountability of positive-measure cells, nullity "
                        + "of representative points, and rate-distortion lower bound remain unresolved."))),
                DescribeRole.Theorem))));
}
