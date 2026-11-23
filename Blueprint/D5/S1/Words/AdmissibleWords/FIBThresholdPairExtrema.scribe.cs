using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.AdmissibleWords;

internal sealed class FIBThresholdPairExtremaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A single threshold realizes all parity-dependent pair extremes of a legal path.",
        H("A shared threshold for real occupancy means"),
        Blocks(Describe.Lean(
            DescribeId.Create("threshold-pair-extrema"),
            DeclarationHandle.Create(
                "D5/S1/Words/AdmissibleWords/FIBThresholdPairExtrema.threshold_pair_extrema"),
            H("Simultaneous pair extremes on a finite path"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Convexity/stanley1986posetpolytopes"),
                LibraryNoteRef.Create("D5/L/Estimation/puccettiwang2015dependence")),
            Blocks(
                Paragraph(Text("For any finite path and any real occupancy profile p in the path "
                    + "stable-set polytope, there is a binary word for each real threshold u. "
                    + "Every word is legal, and the word is empty outside the open unit interval. "
                    + "Each occupied-site event is measurable and has Lebesgue mass p_i. "
                    + "For every pair i,j, the joint occupied mass is min(p_i,p_j) if the two "
                    + "positions have the same parity, and max(0,p_i+p_j-1) otherwise.")),
                Paragraph(Text("Use the interval (0,p_i) at even zero-based positions and "
                    + "(1-p_i,1) at odd positions. Adjacent positions have opposite parity and "
                    + "their two intervals are disjoint because the adjacent occupancies sum to "
                    + "at most one. Same-parity intervals are nested. An opposite-parity pair "
                    + "intersects in an interval of length given by the positive part of its "
                    + "occupancy sum minus one. The event formulas hold for one and the same "
                    + "word map, including zero and unit occupancies.")),
                Paragraph(Text("The order-polytope construction supplies the threshold geometry, "
                    + "and the classical Frechet bounds identify the two extremal pair values. "
                    + "Alternating the interval endpoints enforces the path constraint."))),
            DescribeRole.Theorem))));
}
