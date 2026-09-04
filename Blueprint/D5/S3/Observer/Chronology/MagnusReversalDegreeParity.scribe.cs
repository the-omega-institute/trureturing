using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Chronology;

internal sealed class MagnusReversalDegreeParityDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Chronology/MagnusReversalDegreeParity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Plain chronological reversal negates the second Magnus primitive and preserves the third through the interaction of the Chen antipode with homogeneous grading.",
        H("Magnus Reversal Degree Parity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("magnus-reversal-degree-parity"),
                DeclarationHandle.Create(
                    Prefix + "chronological_reverse_magnus_degree_parity"),
                H("Plain reversal is odd at degree two and even at degree three"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Negating every event acts by the homogeneous grading involution on the factorial step-three signature. Reverse-and-negate is the explicit Chen antipode.")),
                    Paragraph(Text(
                        "The grading involution preserves the second Magnus coordinate and negates the third, while the antipode negates both primitive coordinates.")),
                    Paragraph(Text(
                        "Their combination proves the first two nontrivial cases of the plain-reversal sign law: degree two changes sign and degree three is invariant."))),
                DescribeRole.Theorem))));
}
