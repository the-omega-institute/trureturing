using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class PeriodicRepetitionJointLiftDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Last-cycle-first periodic repetition preserves the literal joint ear",
        H("Last-cycle-first periodic repetition preserves the literal joint ear"),
        Blocks(
            Describe.Lean(DescribeId.Create("periodic-repetition-joint-lift"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/PeriodicRepetitionJointLift.periodic_repetition_joint_lift"),
                H("Every supplied joint witness repeats at its original cut"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let d>=2, 1<=w<=2^(d-1)-1 and m>=2. Fix ANY physical permutation alpha and cut j<=d satisfying OriginalOrder(d,w,alpha) and OriginalOrder(d+1,2w,earWord(d,alpha,j)). Put G=1+2^d+...+2^((m-1)d), K=d*m and U=w*G. The deterministic repeatedWord lists the block r=m-1 first, then r=0,...,m-2; each block replaces label i by r*d+i. This very word satisfies OriginalOrder(K,U), and inserting the single fresh physical label K at the SAME numeric cut j satisfies OriginalOrder(K+1,2U). Both integer totals are zero and every natural take-prefix, including empty, complete and overlong takes, lies in the respective original centered strip. Every physical occurrence remains distinct even when its source value repeats.")),
                    Paragraph(Text("Write q=2^d, B=q/2-1, H=G_(m-1) and R=q^(m-1). A cyclic successor acts only within dimension d+1 or K+1: it takes the base old labels to i+1 and the ear to zero, exactly converting the supplied 2w order into a w order. PeriodicShortening.beta_prefix_bound places its literal last-cycle tail in [0,D], where D=R*(q-1)+(B+w)*H. PeriodicShortening.early_blocks supplies the earlier copies with total -w*H and strip [0,D] starting at w*H. The full physical source cycle has total zero, so the tail ends at w*H. Concatenating tail then early therefore proves legality at the explicit tail boundary, without choosing an arbitrary attained minimum. The literal_ear_identity identifies this exact list with the successor image of earWord(K,repeatedWord,j). No symmetry between different moduli is used.")),
                    Paragraph(Text("The charge corrections are nonnegative and their full r-th block sum is w*q^r. They give the early-copy prefix estimates; the existing tail estimate supplies the last-copy prefixes. The margins are C-D=(q/2-w)*H and D-(w*H+2*G*B)=R-B*H=(B+1)*H+1, with C=2^K-1. The old coordinate reuses ThreeRowSource.repeated_source, scale_strip and scaled_sum: every block has its supplied base heights multiplied by G, total zero, and height at most G*B<=(2^K-2)/2. The new inference is physical coherence of the last-first schedule with the identical old word and literal ear. The independent-order periodic-shortening theorem alone permits an arbitrary minimum rotation and does not preserve this joint witness.")),
                    Paragraph(Text("Applying the generic inference to TwoNegativeJointLift retains its assumptions: w=1+2^a, d=a+b, a,b>=2 and b<a. Repetition m=2 yields the four cyclic gaps (a,b,a,b); arbitrary m yields 2m occupied binary positions. Any other supplied base joint theorem can be repeated with all its hypotheses intact. This conditional periodic transport supplies neither every four-gap orientation nor the unrestricted joint witness. Full physical J and Circle Conjecture C3.1 remain OPEN. This is a repository derivation; no external novelty, finite-search completeness or official acceptance is asserted."))),
                DescribeRole.Theorem)), []));
}
