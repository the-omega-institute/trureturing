using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class WuC5TransferReflectionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Fermionic/WuC5TransferReflection.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The signed five-cycle transfer has an exact scalar reflection product.",
        H("Signed C5 transfer reflection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cycle-sign"),
                DeclarationHandle.Create(Owner + "cycleSign"),
                H("Cycle anticommutation sign"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Wu),
                Blocks(Paragraph(Text(
                    "The cyclic edge relation contributes −1 and every nonedge contributes +1, "
                    + "including the equal-site convention. The independent pairs are directed by "
                    + "the step-two word BᵢBᵢ₊₂."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("word-squares"),
                DeclarationHandle.Create(Owner + "word_squares"),
                H("Five-cycle word squares"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For letters in an algebra over a commutative ring with these signs and arbitrary "
                    + "central scalar squares, the square of the linear word is the sum of the "
                    + "scalar squares plus twice the sum of the five "
                    + "independent-pair words. The square of the pair-word sum is scalar because "
                    + "the five pair words anticommute, while the crossing counts are 3, 1, 1, 3."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("transfer-reflection"),
                DeclarationHandle.Create(Owner + "transfer_reflection"),
                H("Exact transfer reflection"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A SignedCycle consists of five base involutions with the cycle signs and "
                        + "five commuting occupation involutions, each anticommuting only with its "
                        + "own base involution. The grouped transfer collects the "
                        + "empty base word, the five singletons, and the five independent pairs, "
                        + "with unused occupation factors retained.")),
                    Paragraph(Text(
                        "Multiplying the transfer at z and −z gives the scalar reflection polynomial "
                        + "for arbitrary real weights and every complex z. Away from the occupation "
                        + "denominator zeros, the proof factors the transfer into a dressed C5 word "
                        + "and the product of occupation factors. It moves that product through the "
                        + "dressed word at −z, combines the resulting scalar factors, and extends "
                        + "the identity across the finite exceptional set by continuity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("common-reflection"),
                DeclarationHandle.Create(Owner + "transfer_reflection_common"),
                H("Common occupation factor"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When all occupation weights equal a₀, writing l = 1 − a₀²z², "
                    + "S = sumᵢ tᵢ², and D = sumᵢ tᵢ²tᵢ₊₂², the reflection scalar is "
                    + "l³(l² − z²lS + z⁴D). The linear coefficient is the weighted base "
                    + "Hamiltonian plus the common occupation field, and the constant coefficient is I."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "Elman, Chapman, and Flammia (arXiv:2012.07857, Lemma 2) give the bare transfer "
                + "inversion for even-hole-free, claw-free graphs and compute the bare C5 scalar in "
                + "Eq. (100). The occupation-decorated graph contains a claw whose center is a base "
                + "site and whose leaves are its two cycle neighbors and its private occupation "
                + "vertex. The dressed occupation extension is proved in transfer_reflection.")))));
}
