using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra;

internal sealed class FiniteIncidenceGreenDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/HomologicalAlgebra/FiniteIncidenceGreen.";

    private static readonly LibraryNoteRef HodgeSource =
        LibraryNoteRef.Create("D5/L/Geometry/jianglimyaoye2011hodge");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two Green series give incidence-volume bounds for finite real unit repairs. Total unimodularity transfers the smaller applicable bound to a common integral and modular repair.",
        H("Finite Incidence Green Series and Integral Repair"),
        Blocks(
            Paragraph(Text(
                "Let A be a finite real edge-to-face matrix and let a nonzero entry define an adjacency. The Euclidean coordinate spaces use the usual edge and face bases. For a signed simplicial coboundary these are the simplex bases. The real series require the chosen face unit to belong to the real image of A.")),
            Definition("faceBall", "Face ball", "Start at the face f. Each round retains previous faces and adds all faces that share an incident edge with them. After j rounds the face radius is 2j."),
            Definition("edgeBall", "Edge ball", "Take the edges incident to the j-th face ball. The edge radius is 2j+1. Write V_f(j) for the number of edges in this ball."),
            Definition("incidence", "Euclidean incidence operator", "The real matrix acts as a continuous linear map from edge coordinates to face coordinates."),
            Definition("residual", "Neumann residual", "Use Q = I − AAᵀ/M² on face space."),
            Definition("faceUnit", "Face unit", "The Euclidean coordinate vector has value one at f and zero elsewhere."),
            Theorem("residual_pow_vanishes", "Propagation through the face Laplacian", "The j-th residual power applied to the unit vanishes outside the j-th face ball. Each application of AAᵀ connects only faces sharing an edge."),
            Theorem("transpose_residual_pow_vanishes", "Propagation to edges", "The transpose extends the support of the j-th residual power by one incidence step, so the resulting edge vector vanishes outside the j-th edge ball."),
            Definition("neumannTerm", "Neumann term", "Apply Q to power j to the face unit, apply the transpose, and scale by the inverse of M²."),
            Definition("neumannWeight", "Neumann volume weight", "The degree-j majorant is sqrt(V_f(j)) q^j / M."),
            Theorem("neumann_repair", "Real Neumann repair and tail", "Assume 0 < M, 0 ≤ q < 1, operator norm at most M, and residual contraction by q on the image. For a face unit in that image the Neumann terms sum to a solution. The sum of the volume weights bounds its L1 cost. Outside the ball of index J the bound uses the terms of degree J+1 and higher."),
            Theorem("neumann_integer_and_zmod_repair", "Integral transfer of the Neumann bound", "For the real scalar extension of a totally unimodular integer incidence matrix, the same assumptions give an integer solution with L1 cost bounded by the Neumann volume sum. The reduction of this integer solution solves the equation over every ZMod n with support bounded by that sum."),
            Definition("laplacianOnRange", "Face Laplacian on the image", "Restrict AAᵀ to the real image of A."),
            Theorem("residual_contracts_of_spectral_gap", "Neumann contraction from a spectral gap", "Assume 0 < σ ≤ M, operator norm at most M, and lower bound σ² for positive eigenvalues of AAᵀ on the real image. The residual contracts there by q = 1 − σ²/M²."),
            Definition("chebyshevTerm", "Chebyshev term", "Center and scale the face Laplacian on the interval [σ², M²]. Apply the degree-j Chebyshev iterate to the face unit, then the transpose and the corresponding reciprocal-series coefficient. The coefficient uses signed rate (σ − M)/(M + σ) and multiplicity one at zero and two thereafter."),
            Theorem("chebyshevTerm_vanishes", "Chebyshev propagation to edges", "The three-term recurrence gives the same edge radius 2j+1 at degree j."),
            Definition("chebyshevWeight", "Chebyshev volume weight", "For ρ = (M − σ)/(M + σ), the majorant is sqrt(V_f(0))/σ at degree zero and 2 sqrt(V_f(j)) ρ^j / σ at positive degrees."),
            Theorem("chebyshev_repair", "Real Chebyshev repair and tail", "Assume 0 < σ < M, operator norm at most M, and the positive eigenvalue bound σ² on the restricted face Laplacian. For a face unit in the image the series sums to a solution with L1 cost bounded by the Chebyshev volume sum. The tail outside the J-th ball uses degrees J+1 and higher. The proof sums the scalar reciprocal series on the spectral interval and applies it in an eigenbasis of the image."),
            Theorem("spectral_integer_and_zmod_repair", "One integral repair for both Green bounds", "Assume total unimodularity of the integer matrix, real feasibility of the face unit, 0 < σ ≤ M, real operator norm at most M, and lower bound σ² for the positive eigenvalues of the edge Laplacian AᵀA. Positive eigenvalues on the restricted face Laplacian transfer to the edge Laplacian. Choose the real repair with the smaller applicable volume bound and apply integral L1 repair to it.",
                "The integer support is bounded by the integer L1 cost. That cost and every modular support are bounded by the minimum of the two volume sums when σ < M and by the Neumann sum when σ = M. Every reduction uses the same integer witness. The outside-ball tail estimates concern the real series."),
            Paragraph(Text(
                "Jiang, Lim, Yao and Ye provide combinatorial Hodge background. The polynomial approximation and sparse propagation mechanism belongs to the classical inverse-decay and matrix-function literature, including Demko, Moss and Smith, Decay Rates for Inverses of Band Matrices (1984), and Benzi and Razouk, Decay Bounds and O(n) Algorithms for Approximating Functions of Sparse Matrices (2007). The incidence-volume estimates and their application of the repository's integral repair theorem are derived here.")))));

    private static DocumentBlock.Describe Definition(string name, string title, string paragraph) =>
        DescribeDeclaration(name, title, DescribeRole.Definition, paragraph);

    private static DocumentBlock.Describe Theorem(string name, string title, params string[] paragraphs) =>
        DescribeDeclaration(name, title, DescribeRole.Theorem, paragraphs);

    private static DocumentBlock.Describe DescribeDeclaration(string name, string title, DescribeRole role, params string[] paragraphs) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(HodgeSource),
            Blocks(paragraphs.Select(paragraph => Paragraph(Text(paragraph))).ToArray()), role);
}
