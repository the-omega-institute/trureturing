using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.PartialTransposeSaturation;

internal sealed class PartialTransposeSaturationRegularityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Regularity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/wangchen2025partialtranspose");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Regular pencils and partial transpose rank", H("Regularity"),
        Blocks(
            Paragraph(Text("A square complex pencil with no polynomial kernel chain has an invertible scalar combination. If its determinant polynomial vanished, an integral-domain matrix kernel theorem would give a nonzero polynomial kernel vector. Choose the largest degree among its nonzero coordinates. Taking coefficients gives a finite chain with nonzero final coefficient, contradicting the absence of such chains. A nonzero complex determinant polynomial has a nonzero scalar value.")),
            Paragraph(Text("For a complex endomorphism, generalized eigenspaces split into nilpotent Jordan chains. Reversing each chain defines a nondegenerate bilinear pairing making the endomorphism self-adjoint. In matrix coordinates this gives an invertible intertwiner between a matrix and its transpose. Normalizing a regular pair by an invertible scalar combination therefore gives a simultaneous equivalence between both arrows and their transposes. These are constructive steps of the present proof. Classical matrix-pencil decomposition is a precedent, while the finite chain extraction and its splitting are proved directly.")),
            Describe.Lean(DescribeId.Create("tensor-rank-dual-eq-of-reduced"),
                DeclarationHandle.Create(Prefix + "tensor_rank_dual_eq_of_reduced"),
                H("Duality preserves the regular part's tensor rank"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Choose equally indexed finite bases for the square first pair and arbitrary finite bases for the second pair. Dual bases identify dual maps with transposed matrices. The simultaneous transpose equivalence preserves the two-term tensor rank. No independence assumption is needed for the second pair in this equality."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("tensor-rank-pos-of-reduced"),
                DeclarationHandle.Create(Prefix + "tensor_rank_pos_of_reduced"),
                H("A positive-dimensional regular part has positive tensor rank"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("A bijective scalar combination on a positive-dimensional source rules out both arrows being zero. If the other pair is linearly independent, its tensor sum with this nonzero pair cannot vanish: in finite bases, exchange the two tensor coordinates and use coefficient independence. The tensor range is therefore nonzero and its finite rank is strictly positive."))), DescribeRole.Theorem)
        )));
}
