using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence.ConditionalExpansion;

internal sealed class ReverseDoeblinRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Divergence/ConditionalExpansion/ReverseDoeblinRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/hirchegeorgenuradhawilde2026conditional");
    private static readonly LibraryNoteRef Doeblin =
        LibraryNoteRef.Create("D5/L/Divergence/georgehirchenuradhawilde2026doeblin");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Qubit half-depolarization violates the proposed conditional expansion bound.",
        H("Conditional trace-distance expansion and the reverse Doeblin coefficient"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("conditional-trace-expansion-reverse-doeblin-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The proposed conditional expansion bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Equation (2.42) takes the infimum, over finite references and density pairs with "
                    + "positive denominator, of the joint output trace distance minus the reference "
                    + "distance divided by the joint input trace distance minus the reference distance. "
                    + "The paragraph after Proposition 9 asks whether the reverse Doeblin bound applies "
                    + "to that infimum. By Equations (6.54) and (6.55) and Proposition 33 of George et al., "
                    + "the pointwise bound would require every such ratio to be at least one minus p "
                    + "whenever a channel postprocesses N to Z ↦ (1 − p)Z + p Tr(Z)X, with X Hermitian "
                    + "and p in the unit interval."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("conditional-trace-expansion-reverse-doeblin-refutation"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A vanishing conditional ratio for qubit half-depolarization"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source, Doeblin),
                Blocks(Paragraph(Text(
                    "Take N to be the qubit half-depolarizing channel and postprocess by the identity, "
                    + "so p = 1/2 and X = I/2. In reference-first coordinates take the input diagonals "
                    + "(1, 0, 0, 0) and (0, 1/4, 3/4, 0). The joint input difference has trace distance one "
                    + "and the reference distance is 3/4. The output difference has diagonal "
                    + "(11/16, 1/16, −9/16, −3/16), giving trace distance 3/4. "
                    + "The conditional ratio is therefore zero, below the proposed lower bound of 1/2. "
                    + "Proposition 10 of the conditional contraction paper, Equations (5.38) and (5.39), "
                    + "also supplies a witness after evaluating its classical pair at trace distance. "
                    + "Hirche's 2024 vanishing hockey-stick expansion result (arXiv:2405.00105, "
                    + "Appendix B-B, Equations (B.10)–(B.16)) implies the conditional failure by "
                    + "adjoining a binary reference flag."))),
                DescribeRole.Theorem))));
}
