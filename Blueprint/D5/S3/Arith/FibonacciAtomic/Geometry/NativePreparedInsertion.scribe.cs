using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class NativePreparedInsertionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native preparation and two-event insertion for the prepared restriction.",
        H("Native prepared insertion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("native-prepared-insertion-prepares"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/FibonacciAtomic/Geometry/NativePreparedInsertion.prepares"),
                H("Preparation on the actual guarded runner"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Alpha is the true-labelled native leaf and beta the false-labelled leaf. "
                    + "C is the ordered pair (beta,alpha). D(false) is (beta,C), D(true) is "
                    + "(C,beta), and M is ((C,alpha),alpha), with four leaves. For every natural "
                    + "k, preparation starts at alpha and reaches the repository right comb "
                    + "with k copies of C and tail M. It uses exactly 3*k+4 native calls. "
                    + "Each ordinary continuation executes promotion, root split, and left split; "
                    + "the terminal continuation adds a further left-left split. The run equation "
                    + "uses NativeGuardedLeafRepair.run, including its subtree guards and actual "
                    + "replacement, and context_run transports those same calls along the right spine."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-prepared-insertion-endpoint"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/FibonacciAtomic/Geometry/NativePreparedInsertion.prepared_insertion"),
                H("Every order of distinct insertion labels"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every k, every bit assignment on Fin k, and every duplicate-free "
                        + "list of labels, the fixed preparation followed by the flattened "
                        + "two-call insertions succeeds on the original native runner, with total "
                        + "call count 3*k+4+2*length(order). A zero bit "
                        + "promotes then splits the right leaf of C, through (beta,beta), ending "
                        + "at D(false). A one bit splits the left leaf then promotes the right "
                        + "leaf, through (C,alpha), ending at D(true). The addressed slot for "
                        + "zero-based label j is R repeated j times followed by L.")),
                    Paragraph(Text(
                        "The exact endpoint is comb k B M, where B(j)=D(x(j)) for labels "
                        + "in the insertion list and B(j)=C otherwise. The proof transports "
                        + "each local successful trace through the actual native comb and "
                        + "changes only the designated slot. Duplicate-freeness therefore "
                        + "ensures the next slot is still C in every insertion order; guards "
                        + "are checked by the native execution rather than postulated.")),
                    Paragraph(Text(
                        "This proves the source-relative preparation and literal insertion "
                        + "endpoint portion of Proposition 37.1. The unordered coloured quotient, "
                        + "active subset recognition, ordered labelled-bit decoding, current-term "
                        + "recorder reconstruction, update and scratch clearing, payload edit sums "
                        + "and induced peak equalities are separate obligations."))),
                DescribeRole.Theorem))));
}
