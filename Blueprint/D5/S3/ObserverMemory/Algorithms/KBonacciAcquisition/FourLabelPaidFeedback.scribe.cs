using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition;

internal sealed class FourLabelPaidFeedbackDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FourLabelPaidFeedback.";

    private static DocumentBlock Definition(string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Owner + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A full INITIAL family whose second paid endpoint buys an adaptive saving.",
        H("Four labels and exact paid-feedback prices"),
        Blocks(
            Definition("phaseClass", "One phase table on every value and tail",
                "For every integer m at least five, set k=2m-2 and T=k+1=2m-1. The phase argument j is the negative INITIAL phase modulo T, represented from zero through T-1. Class one, named B, occupies m-2,m-1,m; class two, named C, occupies zero,m+1; class three, named D, occupies one; all remaining phases form class zero, named A. An injective map from Fin 4 into an arbitrary label type supplies four pairwise distinct labels. The same class table applies to both scalar values and every legal inherited tail. The independently observed bottom label is arbitrary and may coincide with any live label."),
            Definition("OriginalFiberPresetFeasible", "A preset stream on one full value fibre",
                "A literal stream indexed by the number of blocks actually issued serves every original complete-block history with the specified free INITIAL scalar value. A stop function sees only that saved free output and its own chronological archive. Every chosen word must belong to the original alphabet. Initial bottom stops freely at its immutable target. Correctness quantifies every actual history in the fibre, including all phases and inherited tails, and returns the INITIAL target within the specified number of complete paid words. Rejection remains absorbing and its whole issued word is charged."),
            Definition("FiberPresetPrice", "The fixed-fibre preset minimum",
                "This is the infimum in the extended natural numbers of all feasible finite fibre-preset budgets. It is infinite if there is no feasible finite budget."),
            Definition("selectedSelector", "The saved free value selects one stream",
                "The free INITIAL value selects a literal stream once. At every later issued index the word comes from that stream and the current archive length. Paid replies may select a stop and decoded label, but cannot select a different word. The value is saved even when later endpoint values change."),
            Definition("OriginalSelectedPresetFeasible", "Free-value-selected preset feasibility",
                "One family of streams, indexed only by the saved free INITIAL scalar value, and one stop function must handle every original history under the chosen alphabet. It retains the same complete-word legality, arbitrary bottom label, original joint prior, immutable target, absorbing rejection and bounded paid fee as the GLOBAL preset interface."),
            Definition("SelectedPresetPrice", "The selected-preset minimum",
                "This is the extended-natural infimum of feasible finite selected-preset budgets on the full prior."),
            Definition("rootWord", "The root literal word R",
                "R is the complete m-bit word 0 followed by m-3 ones, then zero, then one. At chronological block index zero its full physical charge support is {1,m-2,m-1,m}. Its first zero clears every inherited legal tail. Its internal runs are shorter than k, and its final tail is one."),
            Definition("leftWord", "The literal word X",
                "X is zero, followed by m-2 ones, then zero. At chronological block index one its full physical charge support is {m+1,0}. It begins by clearing the incoming tail and ends with tail zero."),
            Definition("rightWord", "The literal word Y",
                "Y is m-1 zeros followed by one. At chronological block index one its full physical charge support is {0,1}. Its initial zero clears the incoming tail, and it ends with tail one."),
            Definition("lastWord", "The literal word Z",
                "Z consists of m ones. At chronological block index two its full physical charge support is {1,m+1}. Following X its incoming tail is zero, so m<k makes the entire word safe."),
            Definition("adaptiveSelector", "Two blocks with paid feedback",
                "Initial bottom returns its label immediately. Every live source first issues R. Let the first paid endpoint difference be the first reply plus the saved free value in ZMod 2. Difference zero selects X; difference one selects Y. At the second endpoint it stops, using the second difference to choose A or C on the first branch and B or D on the second. The exact difference codes are A:00, C:01, B:10, D:11. The selector uses only endpoints in its own archive and issues no preparation or cleanup word."),
            Definition("commonStream", "One common literal stream",
                "The stream begins R,X,Z and continues with all-zero m-bit words. The same chronological stream serves both free values and every running archive. A stopped source neither receives nor pays an unissued suffix."),
            Definition("commonStop", "The stopped common decoder",
                "Initial bottom stops before any word. Live sources issue R and X. Those whose first difference is zero stop after X and return A or C according to the second difference. First difference one continues through Z, whose newly acquired difference chooses B or D. Thus the actual stopped difference archives are A:00, C:01, B:100, D:101. No third reading is used on the branches that stop after two."),
            Definition("presetFee", "Exact fees of the common stopped controller",
                "The fee is zero on initial bottom, two on live A and C sources, and three on live B and D sources. It counts actually issued complete words; it is independent of the INITIAL scalar value and inherited legal tail."),
            Describe.Lean(
                DescribeId.Create("original-four-label-paid-feedback"),
                DeclarationHandle.Create(Owner + "original_four_label_paid_feedback"),
                H("Exact two/three-block law on the full original prior"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every m>=5, either original alphabet, any label type Y, any injective labels:Fin 4->Y, and any target f on optional LiveRecord(2m-2) satisfying f(v,-j,s)=labels(phaseClass(m,j)) for every scalar v, every phase j in ZMod(2m-1) and every inherited tail s<2m-2, each fixed-value adaptive minimum is two and each fixed-value preset minimum is three. The full adaptive, free-value-selected-preset and one-stream GLOBAL-preset minima are respectively two, three and three. There is no finiteness assumption on Y and no freshness condition on f(bottom).")),
                    Paragraph(Text(
                        "The lower adaptive bound is the original first-window target-image bound. The actual tail-zero phases below m include representatives two, m-2, zero and one of all four labels. Coprimality gcd(m,2m-1)=1 and the first-window waiting factor one give the lower fee two. Feasibility still includes every original joint history and every inherited tail, not just those four representatives.")),
                    Paragraph(Text(
                        "For the preset lower bound, fix either free value and admit arbitrary scheduled words and arbitrary own-archive stopping. Equal first and second scheduled charges force equal native executions: a root stop, a later stop and simultaneous rejection are all included. Correctness on all actual histories therefore makes equal two-bit codes imply equal labels. Four representative labels inject into the four codes in ZMod 2 times ZMod 2, so they fill the code space. Every phase then has the unique code of its label. Algebraic scheduled charges serve only as invariants in this implication; a stopped source is never granted a later observation.")),
                    Paragraph(Text(
                        "The first physical window has exterior anchors m+2 in class A and m+1 in class C, so A and C have first coordinate zero. The second physical window has exterior anchors two in class A and m-2 in class B, so A and B have second coordinate zero. Injectivity forces A:00, B:10, C:01, D:11. Hence the complete second physical charge is one exactly on {0,1,m+1}. Its sum is one in ZMod 2, contradicting the zero sum of every complete literal charge. All these physical vertices are actual INITIAL phases. The argument covers early stops, rejecting attempts, waits, all-one words and all other original literal actions.")),
                    Paragraph(Text(
                        "The explicit adaptive and preset policies attain the upper bounds on every live value, phase and inherited legal tail. R clears the inherited tail; X and Y clear the next seam; X ends zero before Z. Since m<k, both original alphabets admit every literal m-bit word used here. Native record execution agrees with the original scanner and integer-weight execution, so correctness transports back to every AllowedBlock history, retaining its own INITIAL record and unobserved length.")),
                    Paragraph(Text(
                        "For each original history the theorem supplies an actual stopped PaidTrace returning that history's immutable INITIAL target. The adaptive trace has zero words on initial bottom and exactly two on every live source. The preset trace has precisely presetFee(m,q) words. Flattening each issued complete word gives exactly m bits per archive entry, hence zero or 2m adaptive bits and exactly presetFee(m,q)*m preset bits. For each free value the theorem additionally supplies an actual complete-block history at INITIAL phase minus one and tail zero, together with its own adaptive and common-preset traces emitting exactly 2m and 3m bits. Thus the worst fees are attained on actual sources at both values. Take the selected stream family to be constant, streams(v)=commonStream(m) for every free value v. Then selectedSelector(streams,commonStop(labels,f(bottom))) is definitionally the common presetSelector, for every free value and archive. The same stopped PaidTrace therefore gives selected-preset attainment with exactly 3m emitted bits on each supplied worst history, and the same presetFee(m,q)*m bits on every original history. The separate fixed-value lower bound prevents free value selection from lowering three.")),
                    Paragraph(Text(
                        "This is a repository-derived synthesis of original KBonacci execution, first-window capacity and literal charge parity, for this four-label table and the family k=2m-2. It makes no external priority claim and supplies no exact fee for arbitrary multi-label or tail-sensitive targets, other widths or the uniform all-k/all-m acquisition problem."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("coprime"),
                DeclarationHandle.Create(Owner + "coprime"), H("Every near-critical phase is actual"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every m>=5, gcd(m,2m-2+1)=1. A common divisor divides 2m and 2m-1 and therefore one. Combined with the existing joint-history realization, this arithmetic admits all near-critical INITIAL phases, without revealing INITIAL history length to a controller."))), DescribeRole.Theorem))));
}
