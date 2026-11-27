using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence.ConditionalExpansion;

internal sealed class HeraldedRecoveryUpperBoundDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Divergence/ConditionalExpansion/HeraldedRecoveryUpperBound.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/hirchegeorgenuradhawilde2026conditional");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The success probability of explicit heralded recovery bounds conditional trace expansion.",
        H("Heralded recovery upper bound"),
        Blocks(
          Describe.Lean(
            DescribeId.Create("bell-kernel-recovery"),
            DeclarationHandle.Create(Module + "bellKernelRecovery"),
            H("Bell-kernel recovery map"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Let P be the normalized Bell projector and let Q project onto "
                + "the kernel of amp N(I − P). The completely positive map sums "
                + "congruences by the conjugate reshaping of each column of Q "
                + "divided by √d."))),
            DescribeRole.Definition),
          Describe.Lean(
            DescribeId.Create("heralded-recovery-upper-bound"),
            DeclarationHandle.Create(Module + "heralded_recovery_upper_bound"),
            H("Finite-channel upper bound from heralded recovery"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source),
            Blocks(
                Paragraph(Text(
                    "For every finite channel N from A to B with d = |A| ≥ 2, "
                    + "let P be the normalized Bell projector, X₀ = amp N(P), and Q "
                    + "the orthogonal projection onto the kernel of amp N(I − P). "
                    + "The columns of Q give a rank-one decomposition because QQᴴ = Q. "
                    + "Conjugate reshaping of those columns gives the Kraus family "
                    + "of a completely positive map from B to A.")),
                Paragraph(Text(
                    "The map is trace nonincreasing on every positive semidefinite "
                    + "input. Its composition with N sends every complex matrix X "
                    + "to pX, with p = Re Tr(QX₀)/d² in the interval [0, 1]. "
                    + "Thus on each normalized state the branch succeeds with "
                    + "probability p, independently of the input state.")),
                Paragraph(Text(
                    "For every ε > 0 there are orthogonal density states on the "
                    + "reference Option A and the input A, with positive input gap "
                    + "and actual conditional trace-gap ratio strictly below d²p + ε. "
                    + "Taking the infimum yields η ≤ d²p, and p is feasible for the "
                    + "supremal probability of heralded exact recovery. Equation (2.42) "
                    + "of Hirche, George, Nuradha and Wilde defines the coefficient "
                    + "compared here."))),
            DescribeRole.Theorem))));
}
