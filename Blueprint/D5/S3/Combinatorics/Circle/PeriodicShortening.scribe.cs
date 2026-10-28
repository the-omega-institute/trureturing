using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class PeriodicShorteningDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent shorter orders transport through charged physical blocks",
        H("Independent shorter orders transport through charged physical blocks"),
        Blocks(
            Describe.Lean(DescribeId.Create("periodic-shortening-transport"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/PeriodicShortening.periodic_shortening_transport"),
                H("Independent shorter orders transport through charged physical blocks"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For d>=2, 1<=w<=2^(d-1)-1 and m>=2, EVERY OriginalOrder(d,w,alpha) and independently EVERY OriginalOrder(d+1,w,beta) supply the specified full physical chargedWord at k=d*m+1 and U=w*G_m. It has integer total zero and every pair of natural prefix heights differs by at most D=C-(2^(d-1)-w)*G_(m-1)<C. An attained minimum ell<k gives a rotation that is a permutation of finRange(k), has total zero and has every natural take sum in the ORIGINAL interval [0,C], including overlength takes.")),
                    Paragraph(Text("Early blocks use exponent r*d+i+1, with actual endpoint -w*G_(r+1). The final label map fixes zero and sends j>0 to (m-1)*d+j. On each beta-prefix the SAME surviving phases give Y=2A-E+w*epsilon and Q=A+w*epsilon-w. A may be negative: the proof uses only 0<=Y<=q-1, 0<=E<=w and epsilon in {0,1}. Integer rounding gives -w<=Q<=q/2-1. Thus all original heights lie in [-w*H,R*(q-1)+(q/2-1)*H]. Minimum rotation reuses ZeroSumWordCount.nonnegative_rotate_of_minimum; segment sums are reused from that same owner. Physical permutations retain repeated values as separate labels. The construction removes periodic shortenings in original length induction, since d and d+1 are both smaller than d*m+1. The general cyclic-primitive shortening branch of C3.1 remains open.")),
                    Paragraph(Text("This is a repository derivation of the conditional periodic-shortening construction. The source problem is Damasdi, Frankl, Pach and Palvolgyi, Monochromatic configurations on a circle, Conjecture 3.1. No literature novelty or solution of its general aperiodic case is asserted."))),
                DescribeRole.Theorem)), []));
}
