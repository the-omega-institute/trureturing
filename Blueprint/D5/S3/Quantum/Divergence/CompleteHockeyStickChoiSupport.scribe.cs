using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class CompleteHockeyStickChoiSupportDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/hirchegeorgenuradhawilde2026conditional");

    private static readonly LibraryNoteRef DoeblinSource =
        LibraryNoteRef.Create("D5/L/QuantumChannels/georgehirchenuradhawilde2025doeblin");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The absence of a full reference factor in the Choi support forces unit complete hockey-stick contraction.",
        H("Complete hockey-stick contraction and Choi support"),
        Blocks(
          Describe.Lean(
            DescribeId.Create("complete-hockey-stick-choi-support"),
            DeclarationHandle.Create("D5/S3/Quantum/Divergence/CompleteHockeyStickChoiSupport.result"),
            H("Unit contraction from the normalized Choi support"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source),
            Blocks(
                Paragraph(Text(
                    "Fix a finite channel with nonempty input and a hockey-stick parameter greater "
                    + "than one. If the support of the normalized Choi matrix contains no full "
                    + "reference factor over a nonzero output vector, the complete coefficient "
                    + "for equal-reference-marginal inputs is one.")),
                Paragraph(Text(
                    "Unitary matrices span the reference matrix algebra. Matrix units then recover "
                    + "every output slice of a common support vector. Finite dimensionality "
                    + "reduces the zero intersection to finitely many translates. Preparing the "
                    + "corresponding Bell states gives these translates as basis outputs. The "
                    + "prepared inputs share the added marginal I divided by the input dimension. "
                    + "Data processing bounds the prepared denominator between the output "
                    + "divergence and the original denominator, so each positive output ratio "
                    + "can only increase under this transfer.")),
                Paragraph(Text(
                    "The basis-output support theorem uses the simplex mechanism from Eriksson, "
                    + "Common support and complete contraction with quantum side information, v3, "
                    + "Section 6. Eriksson's criterion concerns Umegaki relative entropy for "
                    + "classical-input channels. The simplex bound used here holds pointwise "
                    + "at the fixed hockey-stick parameter."))),
            DescribeRole.Theorem),
          Describe.Lean(
            DescribeId.Create("complete-hockey-stick-replacement-bound"),
            DeclarationHandle.Create("D5/S3/Quantum/Divergence/CompleteHockeyStickChoiSupport.coefficient_le_of_replacement"),
            H("Contraction bound from a replacement component"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(DoeblinSource),
            Blocks(Paragraph(Text(
                "A channel with a replacement component of weight p has complete coefficient "
                + "at most one minus p for every parameter at least one. Equal input reference "
                + "marginals make the replacement term in the amplified hockey-stick difference "
                + "negative semidefinite. Monotonicity of the positive-part trace and data "
                + "processing for the residual channel give the bound. This is the bound for "
                + "an exhibited weight in Proposition 31 of George, Hirche, Nuradha and Wilde."))),
            DescribeRole.Theorem))));
}
