using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class CyclicGapsPartitionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Recurrence/CyclicGapsPartition",
                "Positive cyclic gaps partition the unit circle."),
            H("Cyclic Gap Partition"),
            Blocks(
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("cyclic-gaps-partition-circle"),
                    H("Cyclic gaps partition the circle"),
                    LeanTheorem(
                        "D5/S1/Recurrence/CyclicGapsPartition."
                        + "cyclic_gaps_partition_circle"),
                    LatexStatement.Create(
                        @"Let $S\subseteq[0,1)$ be a nonempty finite set, and for $x\in S$ "
                        + @"let $g_S(x)=\operatorname{succ}_S(x)-x$ when $x\neq\max S$ and "
                        + @"$g_S(\max S)=(1-\max S)+\min S$. Then "
                        + @"$$\operatorname{succ}_S(x)\in S\quad(x\in S),\qquad "
                        + @"g_S(x)>0\quad(x\in S),\qquad \sum_{x\in S}g_S(x)=1.$$"),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "For a nonempty finite subset of the half-open unit interval, each "
                        + "cyclic successor remains in the subset and every clockwise gap is "
                        + "strictly positive. The successor and predecessor are inverse "
                        + "permutations of the subset, so successor terms cancel against the "
                        + "original points in the total sum. The unique wrap correction then "
                        + "contributes exactly one, and all gaps sum to the circumference.")))))));
}
