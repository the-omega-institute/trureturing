using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence.ConditionalExpansion;

internal sealed class BellCenteredConditionalTraceGapDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Quantum/Divergence/ConditionalExpansion/BellCenteredConditionalTraceGap.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/hirchegeorgenuradhawilde2026conditional");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A normalized Bell-centered pair gives an exact conditional trace-gap quotient.",
        H("Bell-centered conditional trace gaps"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bell-projector"),
                DeclarationHandle.Create(Module + "bellProjector"),
                H("Bell projector"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The projection P is the outer product of the Bell vector in the "
                    + "reference-first basis. For nonempty A (Nonempty A), LiuWildChoiObstruction "
                    + "gives the unit norm of that vector, and CompleteHockeyStickChoiSupport "
                    + "gives the reference marginal I/d for P."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("bell-padded-gap"),
                DeclarationHandle.Create(Module + "bell_padded_gap"),
                H("Exact gaps on the padded reference"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For a finite quantum channel N on input A of size d, "
                        + "put D = d² − 1, C = I − P, and take any input density state ω "
                        + "and 0 < ε ≤ D. This range implies d ≥ 2. "
                        + "The reference is Option A, with exactly d + 1 points. "
                        + "The input matrices are the block diagonals (C, 0)/D and "
                        + "(εP, (D − ε)ω)/D. They are positive semidefinite with trace one "
                        + "and their product is zero.")),
                    Paragraph(Text(
                        "ConditionalHockeyStickOrthogonalReduction supplies the hockey-stick "
                        + "functional, conditional gap, and reference-preserving amplification. "
                        + "At parameter one the reference divergence is (D − ε)/D, so the "
                        + "input gap is ε/D and is strictly positive. The padding block "
                        + "cancels against the unchanged reference contribution after amplification. "
                        + "Writing amp N for the amplified channel, the output gap is the "
                        + "positive-part trace of ε amp N(P) − amp N(C), divided by D. "
                        + "The quotient of output and input gaps is that same trace divided by ε.")),
                    Paragraph(Text(
                        "For this pair, the output gap and the quotient each vanish exactly when "
                        + "ε amp N(P) ≤ amp N(C) in Loewner order. The positive part of the "
                        + "output pencil is positive semidefinite, so it has zero trace precisely "
                        + "when it is zero. This happens precisely when the pencil is negative "
                        + "semidefinite.")),
                    Paragraph(Text(
                        "For nonempty A and ε > 0, tracing the domination gives ε ≤ D because "
                        + "amplification preserves trace, P has trace one, and C has trace D. "
                        + "Choose any input density state for the padding. The orthogonal "
                        + "Option A pair then realizes zero in the orthogonal ratio set at "
                        + "parameter one. The expansion context is Eq. (2.42), Theorem 6 "
                        + "and Proposition 9 of Hirche, George, Nuradha and Wilde."))),
                DescribeRole.Theorem))));
}
