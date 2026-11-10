using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class ActualZhuFiniteDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/ActualZhuFinite.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/popov2026leanvoazhu");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full actual Zhu additive quotient of a positive-definite even lattice is finite-dimensional.",
        H("Finite Dimension of the Full Actual Zhu Quotient"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-zhu-finite-zhuo"),
                DeclarationHandle.Create(Prefix + "zhuO"),
                H("Full actual Zhu O-space"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For any LatticeData D, zhuO(D) is the complex span of the existing full circle(D,n,a,b), "
                    + "where n is natural, a lies in the original energy grade n, and b is any state of Carrier(D). "
                    + "The circle retains every binomial term from j=0 through j=n."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-zhu-finite-positive-definite"),
                DeclarationHandle.Create(Prefix + "positive_definite_zhu_quotient_finite"),
                H("Finite-dimensional full additive quotient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every original LatticeData D with positive-definite real Gram matrix, "
                        + "Carrier(D) / zhuO(D) is finite-dimensional over C. Rank zero and all original charge and oscillator "
                        + "states are included. No determinant-unit, unimodularity, or extra gradedness premise is used.")),
                    Paragraph(Text("The accepted full actual C2-cofiniteness theorem supplies finitely many quotient representatives. "
                        + "Their finite homogeneous projections give a finite homogeneous family S spanning modulo C2. "
                        + "Both unrestricted inputs of each literal C2 generator are expanded in their finite energy supports; "
                        + "projection to energy N retains exactly the homogeneous minus-two pairs with p+q+1=N. "
                        + "Projection of span(S) preserves span(S). The leading term of circle(D,p,a,b) is a_(-2)b; "
                        + "its correction at j=k+1 has energy N-(k+1), strictly below N. Strong induction therefore "
                        + "spans the whole original carrier modulo O by S.")),
                    Paragraph(Text("The circle absorption and degree induction are adapted from Fedor K. Popov's Apache-2.0 "
                        + "Lean_VOA, VOA/Modularity/ZhuAlgebraFinite.lean, commit 013a799ca834a8a6b3afa8129e3e522025b3f45c. "
                        + "The local proof uses the existing actual carrier, fields, energy projections, and circle. "
                        + "This is an algebraic additive-quotient statement; quotient multiplication, rationality, analytic CFT, "
                        + "fusion, anomaly, string theory, and AdS/CFT require further results.")),
                    Paragraph(Text("Four-slot escape registration for this theorem is unfinished. "
                        + "https://github.com/the-omega-institute/trureturing/issues/28685 identifies the missing faithful "
                        + "readout, source reconstruction, law bridge, variation, sensitivity, observational dependence, "
                        + "and source-selection/realization evidence. The issue is not a registration or declared_validated status."))),
                DescribeRole.Theorem))));
}
