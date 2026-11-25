using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class RankThreeInternalTriplePotentialsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/RankThreeInternalTriplePotentials";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Keep the zero-sum mixed triples on the product of a nonzero-dimensional ternary coordinate space and a finite cyclic group. Allow additional triples within each row.",
        H("Ternary Potentials After Adding Internal Triples"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("internal-triples-potential-decomposition"),
                DeclarationHandle.Create(Module + ".potential_iff_separated"),
                H("A row functional and one shared cyclic map"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every normalized potential is the sum of a linear functional of the row and a common additive map of the cyclic coordinate. "
                    + "The additive map must vanish on every cyclic difference of uncovered same-row pairs and on every cyclic-coordinate sum of an internal triple. "
                    + "These two conditions suffice. The mixed-triple equation on an affine line identifies the centered functions on two rows and forces additivity. "
                    + "Negation symmetry and characteristic three give the global zero sum for every separated potential."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("internal-triples-dimension-dichotomy"),
                DeclarationHandle.Create(Module + ".potential_finrank_internal_triples"),
                H("The extra dimension is controlled by the internal residues"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The dimension equals the row dimension plus one exactly when the cyclic group order is divisible by three and all the internal differences and sums reduce to zero modulo three. "
                    + "Otherwise it equals the row dimension. The common additive map is determined by its value at one. "
                    + "Evaluation at zero in the cyclic coordinate recovers the row functional, and evaluation at one in the zero row recovers the allowed cyclic coefficient."))),
                DescribeRole.Theorem))));
}
