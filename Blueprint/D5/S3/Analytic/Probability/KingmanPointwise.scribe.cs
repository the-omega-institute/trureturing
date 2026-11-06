using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Probability;

internal sealed class KingmanPointwiseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "On every finite measure space, nonnegative integrable subadditive cocycles have an integrable invariant real limit almost everywhere.",
        H("Kingman's nonnegative subadditive ergodic theorem"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("kingman-finite-measure"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/KingmanPointwise.kingman_subadditive"),
                H("An integrable invariant limit"),
                StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Asymptotics/durrett2019probability")),
                Blocks(
                    Paragraph(Text("The carrier alpha ranges over every universe u and has an arbitrary measurable-space structure. The measure mu is finite, including zero. The transformation T preserves mu. For each natural n the real function X(n) is integrable and nonnegative almost everywhere. For every m,n, X(m+n,x) is at most X(m,x)+X(n,T^m x) almost everywhere. The exceptional sets may depend on the indices.")),
                    Paragraph(Text("There exists a real function g, integrable for the same mu, invariant under T almost everywhere, such that X(n,x)/n tends to g(x) almost everywhere along the full sequence of natural times. Real division is totalized, so the value at n=0 imposes no additional condition. The original X(0) need not vanish. No pointwise measurability of X(n), nonempty carrier, probability normalization, positive mass, ergodicity, invertibility, countability, standard Borel structure, boundedness or square integrability is assumed.")),
                    Paragraph(Text("When mu is zero, choose g=0; all almost-everywhere conclusions also hold on the empty carrier. For nonzero finite mu, normalize the measure to a probability measure. Its almost-everywhere filter agrees with that of mu, and integrability is equivalent for the two measures. Choose measurable representatives for the functions at positive times and set only the internal zeroth function to zero. Quasi-measure preservation transports their equalities through every orbit shift. Countable intersections produce a measurable forward-invariant set of full measure on which nonnegativity, the zeroth identity and all subadditive inequalities hold together. Setting the family to zero outside that set gives everywhere hypotheses.")),
                    Paragraph(Text("Subadditivity bounds the family by orbit sums of its first term. Fatou's lemma then bounds the integral of the nonnegative extended-real liminf rate and makes that rate finite almost everywhere. The one-step subadditive inequality makes the liminf subinvariant. Measure preservation gives equal integrals for the liminf and its composition; finiteness upgrades their one-sided inequality to equality almost everywhere.")),
                    Paragraph(Text("For each positive epsilon, the sets on which every average up to a horizon exceeds the liminf plus epsilon decrease to a null set. Their first-term integrals tend to zero. The adaptive greedy block estimate bounds each long average by the liminf plus epsilon, an orbit average of the bad-set indicator times the first term, and a terminal strip. Stationary-tail decay removes that strip. The weak maximal inequality makes the remaining excess set null as the bad-set horizon grows. Countably many epsilon levels give the upper limit bound; the definition of liminf gives the lower bound. The real-valued liminf is therefore the integrable invariant limit.")),
                    Paragraph(Text("Transfer this same function g, its integrability and invariance back to mu. Countably many representative equalities identify the original and internal positive-time sequences almost everywhere. Eventual equality transfers convergence without changing g or imposing an identity on X(0).")),
                    Paragraph(Text("Durrett, fifth edition, Section 6.4, Theorem 6.4.1 on printed page 343 with proof on pages 344–347, treats stationary subadditive arrays and also states L1 convergence and an infimum formula. Those further conclusions and a constant ergodic limit are not asserted here. Applying the theorem to a concrete array, matrix product or first-passage model requires the actual common law, shift action, integrability, nonnegativity and subadditive identification. Signed logarithmic cocycles require a separate argument.")),
                    Paragraph(Text("The Lean proof is an attributed adaptation of facebookresearch/atlas-lean, MathlibExt/Dynamics/Ergodic/Kingman.lean, revision a60759060b5616df0d5775b42da4d337719feb32. The Meta Platforms copyright and complete supplier license, including its intended-use preface, are retained. KingmanSigned.exists_invariant_limit_of_nonneg supplies the broad finite-measure specification; no signed-cocycle conclusion is used. The book is a citation-only mathematical source. An equivalent declaration actually available in the host-pinned Mathlib replaces the attributed port."))),
                DescribeRole.Theorem))));
}
