using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.ComplexRadial;

internal sealed class CandidateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed Candidates on the Complex Source Disk", H("Signed Candidates on the Complex Source Disk"), Blocks(
            Paragraph(Text("Fix complex u,v and put R=min(1-norm(u),1-norm(v)). On the disk norm(z)<R, the literal signed J and T formulas at r=z^2 are holomorphic. Source amplitudes use their actual amplitude derivatives. The E denominator uses the stronger norm(u)+sqrt(norm(r))<1 bound, which becomes exactly norm(u)+norm(z)<1; the W branches retain positive real part, and the correction uses the original nonvanishing period. No square-root branch substitution for z is used.")),
            Describe.Lean(DescribeId.Create("norm-lt-sourceradius-iff"), DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Candidate.norm_lt_sourceRadius_iff"), H("norm_lt_sourceRadius_iff"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The disk condition is exactly the conjunction of the two original source norm inequalities."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sourceradius-pos"), DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Candidate.sourceRadius_pos"), H("sourceRadius_pos"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The common disk has positive radius whenever both source coordinates have norm less than one."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sourceradius-le-one"), DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Candidate.sourceRadius_le_one"), H("sourceRadius_le_one"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The common source disk has radius at most one."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("candidate-square-analyticonnhd"), DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Candidate.candidate_square_analyticOnNhd"), H("candidate_square_analyticOnNhd"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For either kernel selector and every sign pair, the literal signed candidate composed with z squared is analytic on a neighborhood of every point in the original common source disk."))), DescribeRole.Theorem))));
}
