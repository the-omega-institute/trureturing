using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class SupportedEigenDimensionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenDimension.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Any 258 selected vertices of Q9 support at least two dimensions of real "
            + "functions with Huang eigenvalue +3.",
        H("Supported Huang eigenvectors on 258 cube vertices"),
        Blocks(
            Paragraph(Text(
                "The functions are on the actual Boolean vertices of Q9. The matrix "
                    + "is the original huangMatrix from HypercubeSubQuorum and "
                    + "Archive.Sensitivity, using the same FALSE-prefix convention as "
                    + "BalancedCriticalSpectrum. TRUE selects the first recursive block. "
                    + "The positive eigenvalue is +3; vector entries are arbitrary real "
                    + "numbers. No degree, regularity, balance or connectedness "
                    + "hypothesis is needed for these linear-algebra interfaces.")),
            Paragraph(Text(
                "The external motivation is Hong, Wu and Xia, Graph Sensitivity of "
                    + "Cartesian Products with Matched Bridges, arXiv:2610.09483v1, "
                    + "Section 7, Problem 2: determine f₂(Q₉)=3 or 4, at "
                    + "https://arxiv.org/html/2610.09483v1#Thmproblem2 . The module reuses "
                    + "the existing Huang family and rank-nullity mechanism to supply "
                    + "inputs for actual component extraction. It makes no novelty, "
                    + "258-vertex witness, exclusion or solution claim. Component "
                    + "extraction and a possible 96-vertex core bound are separate "
                    + "downstream work, with no acceptance claim made here.")),
            Describe.Lean(
                DescribeId.Create("supported-huang-eigen-space"),
                DeclarationHandle.Create(Prefix + "supportedEigenSpace"),
                H("The actual supported +3 eigenspace"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For U : Finset (Q 9), this real submodule consists exactly of "
                        + "functions z with huangMatrix 9 acting by 3z and z(x)=0 "
                        + "whenever x is outside U. Support may be a proper subset of U. "
                        + "The helper mem_supportedEigenSpace_iff exposes this carrier "
                        + "and is consumed by both vector-extraction interfaces."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("supported-huang-eigen-space-dimension"),
                DeclarationHandle.Create(Prefix + "two_le_finrank_supportedEigenSpace"),
                H("258 selected vertices leave dimension at least two"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The sole assumption is U.card=258. Archive.Sensitivity.g 8 is "
                        + "injective from V 8, of dimension 256, and f_image_g gives "
                        + "eigenvalue sqrt(9)=3. The existing coeff 9 linear equivalence "
                        + "and matrix_coeff transport this family to the original "
                        + "Huang matrix on actual Q9 functions. Restrict these functions "
                        + "to the 512-258=254 coordinates outside U. Rank-nullity gives "
                        + "a kernel of dimension at least two. Its injective coordinate "
                        + "map into supportedEigenSpace U proves the stated lower bound. "
                        + "This reuses the existing positive family without assuming "
                        + "the desired supported dimension."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("supported-huang-nonzero-vector"),
                DeclarationHandle.Create(Prefix + "exists_nonzero_supported_eigenvector"),
                H("A nonzero actual supported eigenvector"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For U.card=258, extract a nonzero real function z, zero outside U, "
                        + "with the full ambient equation huangMatrix 9 times z = 3z. "
                        + "It follows from the dimension lower bound and supplies the "
                        + "first vector for the component consumer. No component or "
                        + "sign-switching conclusion is assumed or supplied by this helper."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("supported-huang-vector-vanishing-at-root"),
                DeclarationHandle.Create(
                    Prefix + "exists_nonzero_supported_eigenvector_vanishing_at"),
                H("A nonzero supported eigenvector vanishing at any specified vertex"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For U.card=258 and every specified actual vertex x of Q9, there "
                        + "is a nonzero function w, zero outside U, satisfying the same "
                        + "full +3 eigen-equation and w(x)=0. The vertex x need not "
                        + "belong to U. Evaluation at x maps the supported space to the "
                        + "one-dimensional real field; a domain of dimension at least "
                        + "two gives a nonzero evaluation kernel. The downstream "
                        + "component argument can therefore zero its chosen root while "
                        + "retaining a nonzero vector; propagation along paths belongs "
                        + "to the separate saturation proof."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum"))
        ]));
}
