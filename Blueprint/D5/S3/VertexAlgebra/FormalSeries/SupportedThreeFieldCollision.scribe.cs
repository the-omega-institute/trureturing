using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.FormalSeries;

internal sealed class SupportedThreeFieldCollisionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/VertexAlgebra/matsuo1997locality");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed supported collision with an unchanged spectator coordinate.",
        H("Signed Inner Collision"), Blocks(
            Paragraph(Text("Let F be a bivariate coefficient distribution over a complex algebra, with a lower bound in its second coordinate. Suppose multiplication by (x-y)^N and a nonnegative monomial shift gives the zero extension of a generally infinite native power series P. Only this cleared series is substituted; raw distributions are not substituted or divided by the clearing polynomial.")),
            Describe.Lean(DescribeId.Create("signed-cleared-collision"),
                DeclarationHandle.Create(Prefix + "signed_cleared_collision"),
                H("Finite signed residue fibers and the negative collision region"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For every pair of signed exponents a,b, the original integer-binomial transform has finite support and equals the signed coefficient of P after x=t+y. The second-coordinate lower bound kills every residue index greater than b. For nonnegative a,b the existing cleared_collision_coeff applies.")),
                    Paragraph(Text("When a is negative and b is nonnegative, write r=-a-1. The transform factors as the degree-r binomial kernel applied to the cleared coefficients. Terms of index at most r see a negative first coordinate of P and vanish. Terms of index greater than r have zero binomial weight. This proves cancellation in the negative first-coordinate region without assuming a separate cutoff on an intermediate state."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("slice-extend"),
                DeclarationHandle.Create(Prefix + "slice_extend"),
                H("Signed spectator slice"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The zero extension of a fixed spectator slice equals the three-variable zero extension at that same signed spectator exponent. This index identity is an organizational helper consumed by the actual inner iterate transport."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("clearing-three"),
                DeclarationHandle.Create(Prefix + "clearing_three"),
                H("Finite expansion of the full three-field clearing factor"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Expand the two cross factors and then clear the inner pair. The result equals the action of the complete three-field clearing polynomial on every signed coefficient. This finite polynomial identity is consumed by the actual inner iterate transport and assumes no support bound on the raw distribution."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("inner-collision-coeff"),
                DeclarationHandle.Create(Prefix + "innerCollision_coeff"),
                H("Finite coefficients of the native triangular substitution"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The native substitution sends z0 to z0, z1 to t+z2 and z2 to z2. Every argument has zero constant coefficient, so substitution is legal for arbitrary infinite P. At native index (x,a,b), only indices (x,a+j,b-j) with 0<=j<=b contribute, with weight choose(a+j,a). No finite-support assumption on P is used."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("inner-collision-signed"),
                DeclarationHandle.Create(Prefix + "innerCollision_signed"),
                H("The same collision on each signed spectator slice"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The signed extension of the three-variable native collision equals the bivariate collision of each fixed spectator slice. Every below-support region is included, also when the spectator exponent is negative. The clearing_three identity expands all three pair factors by finite convolution; no analytic convergence or sewing law is asserted."))), DescribeRole.Theorem),
            Paragraph(Text("The binomial-series and locality suppliers retain Carnahan and Matsuo-Nagatomo attribution. These are formal algebraic coefficient identities, with no claim of literature novelty.")))));
}
