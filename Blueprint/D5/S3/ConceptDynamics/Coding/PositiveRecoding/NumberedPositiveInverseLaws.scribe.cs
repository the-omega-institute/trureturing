using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.PositiveRecoding;

internal sealed class NumberedPositiveInverseLawsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact numbered positive recoding and inverse time signs.",
        H("Exact numbered positive recoding and inverse time signs"),
        Blocks(
            Paragraph(Text("For arbitrary rectangular nonnegative matrices R and S, positive_coordinate sends the two half-edges at t to the S half-edge at t joined with the R half-edge at t+1. inverse_coordinate recovers the R half-edge from time t-1 and the S half-edge from time t. translate B a x has coordinate x at t+a for every signed integer a.")),
            Paragraph(Text("positive_translate commutes the literal positive action with signed time. inverse_eq_negative_positive identifies its inverse with the opposite positive recoding followed by translation by -1. Applying this inverse identity and canceling the bijection derives that opposite positive recodings compose to the forward shift. There is no period or nonempty-fiber hypothesis.")),
            Paragraph(Text("These constructions and identities are repository-derived. Their provenance does not assert literature novelty.")),
            Describe.Remark(DescribeId.Create("positive-recoding-numberedpositiveinverselaws-translate"), DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/NumberedPositiveInverseLaws.translate"), H("translate"), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Integer time translation has the literal forward-time sign.")))),
            
            
            Describe.Remark(DescribeId.Create("positive-recoding-numberedpositiveinverselaws-positive-coordinate"), DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/NumberedPositiveInverseLaws.positive_coordinate"), H("positive_coordinate"), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The actual positive law (r_t,s_t) -> (s_t,r_(t+1)).")))),
            Describe.Remark(DescribeId.Create("positive-recoding-numberedpositiveinverselaws-inverse-coordinate"), DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/NumberedPositiveInverseLaws.inverse_coordinate"), H("inverse_coordinate"), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The inverse has preceding time on the recovered R half-edge.")))),
            Describe.Remark(DescribeId.Create("positive-recoding-numberedpositiveinverselaws-positive-translate"), DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/NumberedPositiveInverseLaws.positive_translate"), H("positive_translate"), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The actual positive elementary recoding commutes with every signed integer translation. Both half-edge coordinates use the same translated time.")))),
            Describe.Remark(DescribeId.Create("positive-recoding-numberedpositiveinverselaws-inverse-eq-negative-positive"), DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/PositiveRecoding/NumberedPositiveInverseLaws.inverse_eq_negative_positive"), H("inverse_eq_negative_positive"), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Replacing an inverse by the opposite POSITIVE recoding costs -1.")))))));
}
