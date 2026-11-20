using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9IsotropicHuangDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime-field specialization of the weighted Huang action",
        H("Weighted coordinate flips and supported codewords"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-isotropic-huang-one-parity"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9IsotropicHuang.exists_one_parity_word"),
                H("A nonzero supported weighted eigenvector gives a word on one parity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Integer weights on the signed coordinate flips give an integer matrix whose action over the reals is the corresponding weighted Huang operator. Each flip changes Hamming parity.")),
                    Paragraph(Text("If the integer eigenvalue is divisible by a prime, specialization gives a nonzero modular kernel vector supported within the prescribed set. Splitting by Hamming parity leaves at least one nonzero summand in the kernel.")),
                    Paragraph(Text("This gives a necessary arithmetic test for the separated components in Hong, Wu and Xia's 258-vertex problem in the nine-cube. The weighted action can be tested over finite fields using exact row reduction on the two parity column restrictions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-isotropic-huang-parity-kernel"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9IsotropicHuang.weightedAction_parity_image_eq_kernel"),
                H("Parity exactness over a field at nonzero isotropic weights"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Project onto the bit-true slice for a fixed coordinate and apply its signed flip. The anticommutator of this half flip with the weighted action is the scalar weight in that coordinate.")),
                    Paragraph(Text("At an isotropic weight vector over a field, the weighted action squares to zero. A nonzero coordinate weight makes the half flip a contraction. Both maps exchange parity, so the image on each parity is the kernel on the other. The argument also applies in characteristic two."))),
                DescribeRole.Theorem)),
        []));
}
