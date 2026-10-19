using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.OriginalRoot;

internal sealed class CentralizerTimePowersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A triangle cocycle measures every signed power of the actual time unit.",
        H("Signed time powers of a triangle cocycle"),
        Blocks(
            Describe.Lean(DescribeId.Create("centralizer-time-powers-translated-value"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/OriginalRoot/CentralizerTimePowers.translated_value"),
                H("Every integer time displacement contributes its signed cocycle value"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The declaration is in SourceOnly.CentralizerTimePowers. Its complete Lean statement quantifies a Type* monoid M, A:M, B:M to M to ZMod 3, the triangle equation for every R,V,W, units tau and U with coercion tau=A, and every signed integer s. It evaluates B on tau^s*U and its actual inverse times A. Only tau is constrained by A; U need not commute with A or with another supplied unit.")),
                    Paragraph(Text("centralizer_product gives additivity when the left unit commutes with A. At the identity it gives zero, and at tau times its inverse it gives the negative value for tau inverse. Natural induction then handles tau and tau inverse separately; the integer cases combine into the coefficient s in ZMod 3. Thus a negative displacement contributes a negative multiple, with no replacement by the number of positive letters.")),
                    Paragraph(Text("In the original-action application, A is the actual transition and B is the reduced matrix cocycle. The literal displacement s=-N multiplies the actual time value. PresentationTimeCochain.time_calibration supplies its primitive-orbit interpretation at every positive three-divisible period. The algebraic theorem keeps U arbitrary and imposes neither an inverse for all elements of M nor a native realization of every unit."))),
                DescribeRole.Theorem))));
}
