using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Chronology;

internal sealed class StepThreePrimitiveMagnusDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Chronology/StepThreePrimitiveMagnus.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The denominator-free third Magnus coordinate obeys the exact degree-three BCH law and reverses sign under the Chen antipode.",
        H("Step-Three Primitive Magnus Coordinate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("step-three-primitive-magnus-bch"),
                DeclarationHandle.Create(
                    Prefix + "duodecupled_magnus_degree_three_mul"),
                H("Exact degree-three BCH composition"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Twelve times the third logarithmic coordinate is expressed integrally in the factorial Chen coordinates and vanishes on a single event.")),
                    Paragraph(Text(
                        "Its product law contains the two inherited third coordinates, commutators between first- and second-degree Magnus data, and the two standard nested commutators.")),
                    Paragraph(Text(
                        "The explicit step-three antipode negates this primitive, so reverse-and-negate reverses its chronological orientation."))),
                DescribeRole.Theorem))));
}
