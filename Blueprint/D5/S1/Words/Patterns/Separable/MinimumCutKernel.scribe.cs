using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns.Separable;

internal sealed class MinimumCutKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual minimum-cut events have Cartesian conditional shape laws and literal block labels.",
        H("Actual Minimum-Cut Kernel"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-minimum-cut-cartesian-kernel"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Patterns/Separable/MinimumCutKernel.minimum_cut_cartesian_kernel"),
                H("Minimum-cut shape probabilities on actual avoiders"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("s"), Comma, F.Id("m"), Comma, F.Id("k"), Comma, Sp,
                    F.Id("m"), Gt, D(0), Sp, Land, Sp, F.Id("k"), Gt, D(0), Sp,
                    Rightarrow, Sp, Exists, Sp, F.Id("e"), Colon, Sp,
                    Call("J", F.Id("s"), F.Id("m")), Sp, Times, Sp,
                    Call("U", F.Id("k")), Sp, F.Id("equiv"), Sp,
                    Call("MinimumFiber", F.Id("s"), F.Id("m"), F.Id("k"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For each Boolean sign s and positive natural lengths m and k, U is the actual "
                        + "2413/3142-avoiding permutation subtype, and J consists of its members without "
                        + "a proper cut of sign s. False is direct and true is skew. MinimumFiber is "
                        + "the actual length m+k class with a cut at m and no positive smaller cut. "
                        + "The existential equivalence reconstructs each member by the actual blockSum.")),
                    Paragraph(Text(
                        "For all predicates A on J and B on U(k), the full actual event consisting of "
                        + "block sums of A and B has cardinality card(A) times card(B). Under the "
                        + "uniform PMF on all actual U(m+k), its real probability is this cardinality "
                        + "divided by card(U(m+k)). Dividing by the probability of the minimum-cut "
                        + "fiber gives (card(A)/card(J)) times (card(B)/card(U(k))). Field division "
                        + "is totalized at zero; probability conditioning requires a nonempty fiber.")),
                    Paragraph(Text(
                        "At a left position i the reconstructed zero-based value is "
                        + "(if s then k else 0)+alpha(i); at right position m+j it is "
                        + "(if s then 0 else m)+beta(j). These are literal labels, not standardized "
                        + "flags. The proof establishes the restriction and extension of every "
                        + "smaller same-sign cut, then uses the frozen fixed-cut actual factorization "
                        + "and the pinned Mathlib uniform finite PMF cardinal formula.")),
                    Paragraph(Text(
                        "The minimum cut is not the greatest-cut convention used in the compiled "
                        + "but unfrozen enumeration supplier. Count asymptotics, finite-history truncation, "
                        + "limiting cylinders, occupation, hitting, and the full derangement-ratio "
                        + "limit are not conclusions of this kernel."))),
                DescribeRole.Theorem))));
}
