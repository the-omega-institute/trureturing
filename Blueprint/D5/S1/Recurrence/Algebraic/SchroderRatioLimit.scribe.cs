using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class SchroderRatioLimitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every fixed-shift ratio of native large Schroder counts has an unconditional exact limit.",
        H("Large Schroder Count Ratio Limits"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("large-schroder-fixed-shift-ratio-limit"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/Algebraic/SchroderRatioLimit.schroder_ratio_limit"),
                H("Every Fixed Natural Shift"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Write S(m)=Nat.largeSchroder(m), with S(0)=1 and S(1)=2, "
                        + "and t=sqrt(2)-1. For every fixed natural k, the real ratio "
                        + "S(m)/S(m+k) tends to t^(2k) as m tends to infinity through "
                        + "all natural indices. The theorem has no hypotheses. Its "
                        + "k=0 case has ratio and limit one. Every denominator is "
                        + "strictly positive. The statement gives no uniformity "
                        + "when k is allowed to grow with m.")),
                    Paragraph(Text(
                        "The proof uses the pinned Mathlib formal generating-series "
                        + "identity F=1+XF+XF². For H=XF, formal differentiation and "
                        + "algebra give (1-6X+X²)H'=1+X+(X-3)H. Extracting the "
                        + "coefficient of X^(m+2) yields "
                        + "(m+3)S(m+2)=(6m+9)S(m+1)-mS(m). These are formal-series "
                        + "operations and require no analytic convergence assumption.")),
                    Paragraph(Text(
                        "Set c=t² and q(m)=S(m)/S(m+1). The coefficient recurrence "
                        + "implies q(m+1)(6m+9-mq(m))=m+3. An induction proves "
                        + "0<=q(m)-c and (m+1)(q(m)-c)<=1 for every natural m. "
                        + "The identity c²-6c+1=0 and the bounds 0<=c<=1/4 "
                        + "control the induction. Squeezing against 1/(m+1) proves "
                        + "the adjacent ratio limit. Multiplying finitely many "
                        + "shifted adjacent ratios proves every fixed k. Thus the "
                        + "unbounded tail estimate is established within the proof.")),
                    Paragraph(Text(
                        "The derivation reuses Mathlib's native sequence and formal "
                        + "quadratic identity. It does not postulate a recurrence "
                        + "certificate or replace the sequence by an asymptotic model. "
                        + "This is a repository derivation; no claim of literature "
                        + "novelty is made."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "For the actual permutations avoiding the literal patterns 2413 and "
                + "3142, let A(n) be Nat.card(CutFactorization.Avoider n). The existing "
                + "ActualCardinality.actual_schroder_cardinality theorem gives "
                + "A(0)=A(1)=1 and A(m+1)=S(m). The identity avoider witnesses "
                + "nonemptiness, and the permutation subtype is finite, so A(n)>0 "
                + "for every n. Applying the ratio theorem after the eventual shift "
                + "n=m+1 gives, for every fixed natural k, A(n)/A(n+k) tending to "
                + "t^(2k). The finite prefix is retained; A(n)=S(n-1) is used only "
                + "for positive n.")),
            Paragraph(Text(
                "A distinct application uses the actual signed indecomposable "
                + "avoiders. For either direct or skew sign, the same existing "
                + "cardinality theorem gives twice their count equal to A(n) "
                + "when n>=2. Their fixed-shift ratios therefore have the same "
                + "limit. At length two their count is one while A(2)=2, so these "
                + "are different combinatorial carriers. Both applications reuse "
                + "the exact cardinality correspondence.")),
            Paragraph(Text(
                "These count limits supply no coupled probability law, conditioned "
                + "increment law, cycle filtration or hazard identification for an "
                + "endpoint exploration. Those additional probability-model "
                + "relations require their own proofs.")))));
}
