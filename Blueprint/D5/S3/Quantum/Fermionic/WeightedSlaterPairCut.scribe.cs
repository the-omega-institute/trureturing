using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class WeightedSlaterPairCutDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact purity of the ordinary Slater marginal for disjoint two-site orbitals.",
        H("Purity from binary endpoint differences"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("weighted-ordered-marginal-purity"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Fermionic/WeightedSlaterPairCut.orderedMarginal_purity"),
                H("Purity of the full ordinary marginal"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Split a finite linearly ordered site set into the retained side and " +
                        "its complement. Choose disjoint pairs on each side and order each " +
                        "pair from its earlier endpoint to its later endpoint. Assign a complex " +
                        "amplitude to each endpoint, allowing zero. Form the ordered Slater " +
                        "cut matrix B using retained-first column order.")),
                    Paragraph(Text(
                        "Let A be the binary matrix whose entries record whether the endpoints " +
                        "of two pairs alternate in site order. The trace of the squared Gram " +
                        "matrix of B is a sum over binary retained endpoint differences. " +
                        "For each difference string, multiply the retained endpoint mass " +
                        "autocorrelations by the square of the product of discarded endpoint " +
                        "character sums. The character exponents come from the transpose of A " +
                        "applied to the difference string. An endpoint mass is the squared " +
                        "modulus of its amplitude. The identity holds for unnormalized weights.")),
                    Paragraph(Text(
                        "On occupations selecting one endpoint from each pair, the ordered " +
                        "determinants give separate amplitude products and the character of " +
                        "the cross interaction. Multiplying a Gram entry by its transpose " +
                        "partner cancels the separate phases and squares the discarded " +
                        "character sum. Translating the second retained string by the first " +
                        "makes their difference the outer summation variable. The remaining " +
                        "sums factor over individual endpoints. Isometric padding preserves " +
                        "the trace on the full occupation space."))),
                DescribeRole.Theorem))));
}
