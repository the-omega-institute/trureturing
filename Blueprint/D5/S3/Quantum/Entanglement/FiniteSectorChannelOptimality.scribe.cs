using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class FiniteSectorChannelOptimalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The common residual spectra determine the exact channel error for sector coarse-graining under arbitrary local quantum operations and finite shared classical mixtures.",
        H("Finite Sector Channel Optimality"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-sector-actual-channel-optimality"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/Entanglement/FiniteSectorChannelOptimality.result"),
            H("The residual Gram minimum determines the optimum"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The logical sectors form a nonempty finite set. Each sector has a positive "
                    + "target rank and a common finite list of nonnegative residual spectral values. "
                    + "The list is decreasing and sums to one. The source encoding repeats each "
                    + "residual coefficient across the target coordinates, with the normalization "
                    + "given by the sector rank. The target encoding is flat on those coordinates.")),
                Paragraph(Text(
                    "The residual Gram kernel pairs the square roots of the two sectors' spectra. "
                    + "Its minimum quadratic form is taken over all probability vectors on the "
                    + "logical sectors. The optimum unhalved diamond error is twice one minus this "
                    + "minimum. The same value is the infimum over arbitrary products of local "
                    + "completely positive trace-preserving maps and over finite probability "
                    + "mixtures of such products. An actual product channel attains the value.")),
                Paragraph(Text(
                    "Both encodings are actual isometric quantum channels. Each arbitrary local "
                    + "channel pair has an actual joint realization, and each finite shared "
                    + "classical mixture has an actual mixture realization. These realizations "
                    + "agree on every input matrix. The diamond error ranges over every finite "
                    + "passive reference and every joint density input, so the reference can "
                    + "retain correlations with the logical sector.")),
                Paragraph(Text(
                    "Complete positivity makes the channel's Choi matrix positive. Its spectral "
                    + "decomposition gives a finite Kraus family, and trace preservation makes "
                    + "that family complete. Stacking the Kraus matrices gives the finite "
                    + "isometric environment used in the channel constructions and competitor bounds.")),
                Paragraph(Text(
                    "Tracing out the residual coordinate on each side gives the attaining "
                    + "product, using the same local splitting channel on both sides. Its "
                    + "partial-trace action is specified on every physical input matrix. On "
                    + "every encoded logical matrix, the joint action is multiplication by "
                    + "the residual Gram kernel followed by the target encoding. In particular, "
                    + "each logical basis sector produces its exact target pure state. The "
                    + "same encoding and joint channel have the stated diamond error and "
                    + "both stated infima. The kernel "
                    + "is positive semidefinite, has diagonal one, and has entries at most one. "
                    + "Pure joint inputs give a rank-one positive matrix minus a positive "
                    + "matrix of equal trace. The positive spectral part has rank at most one, "
                    + "which bounds the trace norm by the maximal complementary quadratic form. "
                    + "Spectral convex decomposition extends this bound to every density input.")),
                Paragraph(Text(
                    "A common correlated reference test gives the lower bound against each "
                    + "arbitrary local competitor. The singular-value prefix constraints of "
                    + "the same Stinespring realization control its overlap with the flat target. "
                    + "The same test also controls finite shared classical mixtures, since "
                    + "its target overlap is linear in the output state. Compactness of the "
                    + "sector probability simplex supplies a minimizing test and identifies "
                    + "both infima with the error of the residual-trace product.")),
                Paragraph(Text(
                    "For arbitrary positive flat source and target ranks, exact output on "
                    + "every basis sector is possible if and only if each source rank is a "
                    + "positive integer multiple of its target rank. Necessity follows from "
                    + "the actual local Stinespring isometries: purity forces the joint "
                    + "amplitude to factor through the target vector, and the resulting "
                    + "environment projection has integer rank. Sufficiency splits each "
                    + "source coordinate into its target and residual coordinates by a "
                    + "sector-dependent finite equivalence, constructs a common local "
                    + "isometry, and traces out its environment."))),
            DescribeRole.Theorem))));
}
