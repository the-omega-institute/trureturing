using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.MomentMinors;

internal sealed class PairMinorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive semidefinite kernels of second minors.",
        H("Second minors"), Blocks(
            Describe.Lean(DescribeId.Create("moment-pair-minor-positive"),
                DeclarationHandle.Create("D5/S3/Analytic/MomentMinors/PairMinor.pairMinor_posSemidef"),
                H("Positivity for arbitrary index pairs"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a finite real positive semidefinite matrix A and any finite family of ordered pairs (p(a),q(a)), the matrix with entries A(p(a),p(b)) A(q(a),q(b)) - A(p(a),q(b)) A(q(a),p(b)) is positive semidefinite. Pairs may repeat, coincide, or overlap.")),
                    Paragraph(Text("In the tensor square, send each pair to the difference of its two ordered coordinate vectors. Congruence of A tensor A by this map gives twice the displayed matrix. Positivity follows from positivity of the Kronecker product, congruence, and multiplication by the nonnegative scalar one half."))),
                DescribeRole.Theorem))));
}
