using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.HiguchiSudbery;

internal sealed class ReflectionEvaluationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Polynomial evaluation and nonnegativity for the four-qubit entropy certificate.",
        H("ReflectionEvaluation"),
        Blocks(Paragraph(Text("The generic square law ref_eval_square_nonneg proves nonnegativity for any polynomial with a nonnegative integer weight. The evaluations ref_eval_m0 through ref_eval_m47 use literalMinor at the corresponding indices. The resulting identities ref_eval_lhs and ref_eval_rhs_nonneg connect the certificate to the marginal third elementary symmetric sums.")))));
}
