using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.FormalSeries;

internal sealed class SupportedFourFieldCollisionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/FormalSeries/SupportedFourFieldCollision.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Admissible native arguments", H("Admissible native arguments"), Blocks(
            Describe.Lean(DescribeId.Create("supportedfourfieldcollision-fourinner-hassubst"),
                DeclarationHandle.Create(Prefix + "fourInner_hasSubst"),
                H("Admissible native arguments"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The four native power series arguments are X0, X1, X2+X3 and X3. Each has zero constant coefficient, so substitution is defined for a generally infinite input series."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("supportedfourfieldcollision-fourinnercollision-coeff"),
                DeclarationHandle.Create(Prefix + "fourInnerCollision_coeff"),
                H("Finite collision coefficients"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a generally infinite four-variable series P over a commutative complex algebra, the coefficient at x,y,a,b after native collision equals the sum over 0 through b of choose(a+j,a) times the original coefficient at x,y,a+j,b-j. Both spectator labels remain fixed. The finite fiber follows from the substituted monomial coefficients, without any finite-support assumption on P."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("supportedfourfieldcollision-slice-extend"),
                DeclarationHandle.Create(Prefix + "slice_extend"),
                H("Two signed spectator slices"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fixing two signed spectator indices defines a native bivariate slice of the same original P. Its zero extension equals the four-variable signed extension on those fixed indices, including negative collision and spectator regions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("supportedfourfieldcollision-fourinnercollision-signed"),
                DeclarationHandle.Create(Prefix + "fourInnerCollision_signed"),
                H("Signed native collision"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The signed extension of the native four-variable collision equals the existing bivariate collision on the fixed two-spectator slice. Every signed coordinate is allowed. If either spectator index is negative the slice and both readouts vanish. Carnahan binomial collision identities are retained through the bivariate supplier."))), DescribeRole.Theorem))));
}
