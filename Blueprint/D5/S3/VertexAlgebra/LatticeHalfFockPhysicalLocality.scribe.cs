using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockPhysicalLocalityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Charged half-Fock coefficients satisfy two-sheet physical locality on every actual tensor state.",
        H("Charged Physical Locality"),
        Blocks(
            Paragraph(Text("For arbitrary integral symmetric even lattice data D, an integer determinant unit hu, "
                + "charges left and right, integer exponents first and second, and every state in the dependent "
                + "actual tensor representation, set N=(bilinear D left right).natAbs. The coefficient identity "
                + "uses the physical shifts first-2*(N-offset) and second-2*offset and is independent of the "
                + "exponent pair and target state.")),
            Paragraph(Text("The proof expands both ordered products through one bivariate polynomial kernel with "
                + "rectangular finite support, clears both half-contraction branches by (1-t^2)^N, uses the "
                + "actual cocycle product and exchange including its normalization, and identifies the resulting "
                + "finite signed binomial sum with the iterated doubled-shift difference. The pure tensor result "
                + "is lifted to every ActualTensor vector by TensorProduct induction.")),
            Describe.Lean(
                DescribeId.Create("latticehalffockphysicallocality-charged-coefficient-physical-locality"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockPhysicalLocality.charged_coefficient_physical_locality"),
                H("Uniform two-sheet locality of charged coefficients"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every D, hu, left, right, first, second and state in the original telescope, "
                        + "the displayed sum over Finset.range (N+1), with coefficient ((-1)^offset)*choose(N,offset), "
                        + "annihilates the difference of the two chargedCoefficient compositions. N is fixed before "
                        + "first, second and state. No positivity, rank, homogeneity, branch, eigenstate or locality "
                        + "hypothesis is added."))),
                DescribeRole.Theorem),
            Paragraph(Text("Bakalov–Kac, arXiv:math/0402315, section 4.1, supplies the two opposite cover branches "
                + "and the ordered-product mechanism. The actual quotient ground representation and the native "
                + "half-creation transport are used directly from the canonical library.")),
            Paragraph(Text("This result is algebraic and kernel-checked. Corrected normal-word locality, source-product "
                + "compatibility, twisted Jacobi, analytic CFT completion, fusion and anomaly data, Moonshine, string "
                + "theory and AdS/CFT remain separate obligations.")))));
}
