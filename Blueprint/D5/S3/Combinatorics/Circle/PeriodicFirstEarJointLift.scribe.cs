using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class PeriodicFirstEarJointLiftDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Physical periodic first-ear joint order",
        H("Physical periodic first-ear joint order"),
        Blocks(
            Describe.Lean(DescribeId.Create("periodic-first-ear-joint-lift"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/PeriodicFirstEarJointLift.periodic_first_ear_joint_lift"),
                H("The natural physical word and its first ear"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every d>=2 and m>=1, put k=d*m, N=2^k-1 and t=N/(2^d-1). The theorem proves OriginalOrder k t (List.finRange k) together with OriginalOrder (k+1) (2*t) (earWord k (List.finRange k) 0), using the existing native predicates and insertion word. Both conclusions retain their complete physical inventories, exact integer zero totals and all natural prefix lengths, including empty, full and overlong prefixes.")),
                    Paragraph(Text("Write T=t and r=2^d. The quotient relation is (r-1)T=N. The actual old source is m consecutive copies of [T,2T,...,2^(d-2)T,-(2^(d-1)-1)T]. For n<=k its natural prefix height is H_n=T*(2^(n mod d)-1); for n>k it is zero. Thus H_n>=0 and 2H_n+T<=N. The d=2 case uses the actual centered base [1,-1], so neither d=2 nor m=1 is excluded.")),
                    Paragraph(Text("The native digit_data and charge_sum results give nonnegative physical charges q_i, total charge T and the exact old-label equation g(i)=2f(i)-q_i at the new modulus 2^(k+1)-1. The fresh physical label k has value T. Inserting it first makes the height after n old labels equal to T+2H_n-Q_n, where 0<=Q_n<=T. The reserve inequality bounds this height between zero and N, the new half-modulus. Both full sums vanish by the actual source cycle.")),
                    Paragraph(Text("Repeated numerical values never identify physical labels: the old carrier is Fin(d*m), the word contains every old occurrence, and only the fresh label k is added. No numerical period is asserted for the new source. This arbitrary-count structured family does not complete the general period-quotient problem or Circle C3.1."))),
                DescribeRole.Theorem)), []));
}
