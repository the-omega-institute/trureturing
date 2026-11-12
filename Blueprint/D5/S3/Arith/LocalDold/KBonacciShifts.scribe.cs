using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.LocalDold;

internal sealed class KBonacciShiftsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive-seed k-bonacci shifts", H("Positive-seed k-bonacci shifts"), Blocks(
            Paragraph(Text("These historical proof bodies apply the Ma-Zhang backward-zero mechanism, deriving the negative zero from the recurrence. The order-three and order-four scalar seeds motivate the result. The all-order normalized impulse block theorem remains a separate obligation. Registration remains unfinished under issue 29392.")),
            Describe.Lean(DescribeId.Create("kbonaccishifts-adjacent-doubling-no-repair"),
                DeclarationHandle.Create("D5/S3/Arith/LocalDold/KBonacciShifts.adjacent_doubling_no_repair"),
                H("adjacent_doubling_no_repair"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Scale/mazhang2026backwardzero")),
                Blocks(Paragraph(Text("For a bilateral integer order n+1 k-bonacci recurrence with every positive seed through n+1 positive, an adjacent doubling at 0<i<n+1 forces a strictly negative-time zero. At every prime and every nonnegative shift there is no fixed positive local-Dold repair. The proof constructs the integral invertible companion action and proves positivity from the actual seeds."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("kbonaccishifts-one-two-seeds-no-repair"),
                DeclarationHandle.Create("D5/S3/Arith/LocalDold/KBonacciShifts.one_two_seeds_no_repair"),
                H("one_two_seeds_no_repair"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Scale/mazhang2026backwardzero")),
                Blocks(Paragraph(Text("For k>=3, a bilateral integer k-bonacci recurrence with a(1)=...=a(k-1)=1 and a(k)=2 has no positive local-Dold repair at any prime and any nonnegative shift. The positive-seed hypothesis is not the normalized impulse block initial condition."))), DescribeRole.Theorem))));
}
