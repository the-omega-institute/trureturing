using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.CausalMoments;

internal sealed class FiniteMomentSupportReductionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/CausalMoments/FiniteMomentSupportReduction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite rational causal laws can be compressed relative to the linear information actually retained. The global joint feature profile exposes indistinguishable states and affine redundancy, while Caratheodory supplies a positive law-specific latent witness controlled by profile rank rather than the full response-table cardinality.",
        H("Finite moment support reduction for causal response laws"),
        Blocks(
            Describe.Lean(DescribeId.Create("law-moment-vector"), DeclarationHandle.Create(Prefix + "lawMomentVector"), H("Retained moment vector"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Collect a finite family of rational atom features into their expectation vector under one normalized response law."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("profile-affine-rank"), DeclarationHandle.Create(Prefix + "profileAffineRank"), H("Affine rank of joint atom profiles"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Measure the affine dimension of the range of the retained feature map. Duplicate profiles and affine dependencies do not increase this rank."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("law-moment-vector-convex-hull"), DeclarationHandle.Create(Prefix + "lawMomentVector_mem_convexHull"), H("Moments lie in the atom-profile convex hull"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Normalization and nonnegativity express the retained moment vector as a convex combination of original atom profiles."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("moment-compression"), DeclarationHandle.Create(Prefix + "MomentCompression"), H("Positive sparse moment witness"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A compression stores original feature profiles, positive normalized weights, exact moment equality, affine independence, and a finite cardinality bound."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("exists-moment-compression"), DeclarationHandle.Create(Prefix + "exists_momentCompression"), H("Every finite law has a small exact moment witness"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Mathlib Caratheodory reduction selects an affinely independent positive atomic representation of the exact moment vector."))), DescribeRole.Theorem),
            
            
            
            
            
            
            
            Describe.Lean(DescribeId.Create("linear-row-query-feature"), DeclarationHandle.Create(Prefix + "linearRowQueryFeature"), H("Join LP rows and one query"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Constraint rows occupy some coordinates of an Option index and the none coordinate stores the objective."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("linear-problem-profile-rank"), DeclarationHandle.Create(Prefix + "linearProblemProfileRank"), H("Constraint-aware LP profile rank"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Take the affine rank of the joint vector consisting of every LP row coefficient and the objective coefficient on each original atom."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("linear-problem-profile-rank-le"), DeclarationHandle.Create(Prefix + "linearProblemProfileRank_le"), H("Profile rank is bounded by the raw row count"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The joint LP profile rank is at most the number of constraint rows plus the one objective coordinate."))), DescribeRole.Theorem),
            
            
            
            
            Describe.Lean(DescribeId.Create("finite-linear-problem-small-latent-witness"), DeclarationHandle.Create(Prefix + "finite_linear_problem_small_latent_witness"), H("Every feasible query point has a small attaining latent model"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Every feasible finite linear causal law admits an attaining positive latent realization with at most the row count plus two states."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("response-table-cell-query-feature"), DeclarationHandle.Create(Prefix + "responseTableCellQueryFeature"), H("All response-cell marginals plus one query"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For k Boolean response-pair strata, retain all four one-stratum response-cell indicators and one scalar query."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("exists-response-table-cell-query-compression"), DeclarationHandle.Create(Prefix + "exists_responseTableCellQueryCompression"), H("Linear-size witness inside the four-to-the-k table space"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Although the unrestricted response-table carrier has four to the k atoms, all one-stratum four-cell marginals and one query have a positive witness using at most four k plus two atoms."))), DescribeRole.Theorem))));
}
