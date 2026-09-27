using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.AnalyticClosure.Polylogarithm;

internal sealed class CompositionZeroFreeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive-composition normalized source series is zero-free on the unit disk.",
        H("CompositionZeroFree"), Blocks(
            Describe.Lean(DescribeId.Create("all-composition-disk-theorem"),
                DeclarationHandle.Create("D5/S3/AnalyticClosure/Polylogarithm/CompositionZeroFree.result"),
                H("The complete source-specific disk consumer"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/AnalyticClosure/xu2026rational"),
                    LibraryNoteRef.Create("D5/L/AnalyticClosure/miller1978starlike")),
                Blocks(Paragraph(Text(
                    "For every head:PNat and tail:List PNat, let d=tail.length+1 and "
                    + "F(z)=sum_n (H(tail,n+d-1)/(n+d)^head) z^n. Set L(z)=z^d F(z), "
                    + "Q(0)=d, and Q(z)=z L'(z)/L(z) away from zero. The defining F series "
                    + "is absolutely convergent for every |z|<1. Both F and Q are analytic on "
                    + "that disk, F never vanishes there, and Re Q is strictly positive everywhere, "
                    + "including zero. There are no additional recurrence, coefficient estimate, "
                    + "analyticity, first-contact or zero-freeness assumptions.")),
                    Paragraph(Text(
                    "The proof keeps the classical first-contact argument local: a compact minimal "
                    + "contact radius, the angular derivative and the inward radial derivative "
                    + "contradict the normalized differential equation. The quotient g/h is formed "
                    + "using only the induction hypothesis that h is nonzero; nonvanishing of g is "
                    + "a conclusion. Induction on the tail and the positive head uses the two actual "
                    + "source recurrences. Continuity extends the normalized equation at zero, "
                    + "and a direct derivative calculation identifies the explicitly extended Q.")),
                    Paragraph(Text(
                    "This is an intermediate disk theorem toward Xu-Zhao Conjecture 1.3. It makes "
                    + "no full-conjecture resolution or originality claim and receives zero "
                    + "solved-problem credit. Boundary convergence, slit continuation, bank estimates, "
                    + "formal-inverse coefficient realization and finite-contour sign transfer "
                    + "remain separate obligations. No global slit zero-freeness or univalence "
                    + "for depth greater than one is asserted."))), DescribeRole.Theorem))));
}
