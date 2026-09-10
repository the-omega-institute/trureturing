using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History.Spacetime;

internal sealed class CoordinateEncodingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-dimensional coordinates and four event attributes have exact literal HF tuple codes.",
        H("Coordinate and Attribute Tuples"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-position-code-equivalence"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/CoordinateEncoding.position_code_equiv"),
                H("An arbitrary fixed finite dimension"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A recursive tuple grammar contains exactly the prescribed number of integer entries, "
                    + "followed by an empty-set terminator. The representation applies Mathlib's Fin.consEquiv "
                    + "and the proved integer coding equivalence."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("event-attributes-code-equivalence"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/CoordinateEncoding.attributes_code_equiv"),
                H("All four attributes are preserved"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The tuple stores time, position, sign and source tree in that order. Its sign component "
                    + "is exactly the integer code of positive or negative one. Component equivalences supply "
                    + "both round trips without assumed compatibility fields."))),
                DescribeRole.Definition))));
}
