using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;
internal sealed class DiagonalHeatDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Analysis/DiagonalHeat.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual algebraic diagonal operator has a self-adjoint closure and a positive whole-space heat with precisely its full negative generator graph.",
        H("Diagonal Hamiltonian and Strong Heat"),
        Blocks(
            Definition("finiteOperator", "The finite algebraic operator",
                "For every full complex Hilbert basis e of a complete Hilbert space and every real family h, this partial complex linear map has domain exactly the algebraic span of the range of e. LinearIndependent.repr supplies its finite coefficients; Finsupp.linearCombination synthesizes the basis vectors weighted by h."),
            Definition("hamiltonian", "The actual closure",
                "For the same arbitrary full basis e and real family h, the Hamiltonian is the actual LinearPMap closure of finiteOperator e h. The main theorem proves self-adjointness for nonnegative h and identifies the entire graph and weighted-l2 domain."),
            Definition("multiplier", "The bounded full-space multiplier",
                "For an arbitrary full basis e, real coefficients a, nonnegative real M and a proof that every absolute coefficient is at most M, transport the actual bounded l2 diagonal multiplier through e.repr. The resulting map is a bounded complex linear endomorphism of the entire ambient Hilbert space."),
            Definition("heat", "The whole-space heat",
                "For an arbitrary full basis e and nonnegative real family h, at each nonnegative-real time t take the full-space multiplier with coefficient exp(-t*h(i)) and bound one. Zero eigenvalues give coefficient one and zero time gives the identity."),
            Result("finite_basis", "The exact finite-span basis action",
                "For every actual full complex Hilbert basis e, arbitrary real coefficient family h and index i, finiteOperator e h maps the genuine domain vector e(i) to h(i) times e(i). The finite representation of e(i) is the single coefficient one at i. This exact action supplies both the self-adjoint closure theorem and the finite graph approximants used for the lower quadratic-form bound."),
            Result("multiplier_coeff", "Actual bounded coordinate action",
                "Let H be a complete complex Hilbert space and e an actual full Hilbert basis indexed by any type I. Let a be a real family with absolute value at most the nonnegative real M. Transport multiplication by a through the isometric coefficient map from H to l2(I,Complex). This defines a bounded complex linear operator on all of H. For every vector x and every i, its i-th coefficient is a(i) times the coefficient of x. The bound is proved on the actual l2 multiplier before extending the action to H."),
            Result("multiplier_basis", "Basis vectors remain genuine eigenvectors",
                "Under the same assumptions, the actual multiplier sends e(i) to a(i) times e(i). Coordinate injectivity and the single-coordinate expansion prove the equality, including zero and repeated coefficients. These coordinate and vector identities also determine the heat and resolvent operators."),
            Result("multiplier_positive", "Positivity on the whole Hilbert space",
                "If all a(i) are nonnegative, the actual bounded multiplier is positive. Parseval expresses its quadratic form as the genuinely convergent sum of a(i) times the squared modulus of the coefficient of x. Each term is real and nonnegative. This proves positivity and self-adjointness on the entire space, without a finite-dimensional hypothesis."),
            Result("diagonal_heat", "The same closure has the full strong heat generator",
                "Let h(i) be finite nonnegative real coefficients. Define T0 on exactly the algebraic span of the full basis: apply LinearIndependent.repr to obtain finite coefficients and then Finsupp.linearCombination to synthesize the h-weighted basis vectors. Set K to the genuine partial-map closure of T0. The accepted real-eigenbasis closure theorem proves K self-adjoint and densely defined. Its full graph consists precisely of pairs (x,y) satisfying c(i,y)=h(i)*c(i,x) for every i. Its actual operator domain consists precisely of x whose h-weighted coefficients belong to l2. This domain need not be all of H.",
                "For nonnegative time t, define T(t) as the bounded multiplier exp(-t*h(i)). It is positive, complex linear and contractive on all of H. There exists a strongly continuous contraction semigroup S whose real operators are exactly the scalar restrictions of T(t). Thus T(0) is the identity, T(s+t)=T(s) composed with T(t), and every orbit is continuous, including at zero.",
                "For all ambient vectors x and v, the right strong limit of (T(t)x-x)/t as t tends to zero exists and equals v if and only if (x,-v) belongs to the graph of this same K. The forward implication uses each continuous coefficient functional and the scalar exponential derivative. For the reverse implication, the full graph-core theorem gives simultaneous finite-vector and operator-image approximants; closedness of the semigroup generator passes the finite derivatives to their graph limit. Any other strongly continuous contraction semigroup with this full generator graph equals S by the accepted generator uniqueness theorem.",
                "All basis index types, empty and finite cases, repeated coefficients and zero eigenspaces are retained. No heat trace at time zero is asserted. The proof adapts the generic private heat construction in PhysicalHeatGenerator and uses the public general ContractionSemigroup closedness and uniqueness suppliers selected from Scott Armstrong with their Apache-2.0 source attribution. This is a standard diagonal operator construction, not a common-reference theorem for a family of quantum states."))));
    private static DocumentBlock.Describe Result(string name, string title, params string[] paragraphs) =>
        Describe.Lean(DescribeId.Create("diagonal-heat-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(paragraphs.Select(p => Paragraph(Text(p))).ToArray()),
            DescribeRole.Theorem);
    private static DocumentBlock.Describe Definition(string name, string title, params string[] paragraphs) =>
        Describe.Lean(DescribeId.Create("diagonal-heat-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(paragraphs.Select(p => Paragraph(Text(p))).ToArray()),
            DescribeRole.Definition);

}
