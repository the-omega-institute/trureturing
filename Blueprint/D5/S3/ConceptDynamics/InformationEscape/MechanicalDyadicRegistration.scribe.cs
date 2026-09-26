using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class MechanicalDyadicRegistrationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscape/MechanicalDyadicRegistration.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dyadic mechanical boundary registrations retain the complete parameterized readouts.",
        H("MechanicalDyadicRegistration"),
        Blocks(
            Node("mechanicalReadoutSignature", "One Unit-indexed CUT slot returns a typed "
                + "observation; there are no anchor slots."),
            Node("mechanicalReadoutRealization", "The realization returns its supplied "
                + "observation function without reducing it to a theorem's truth value."),
            Node("LowerOutput", "A slope and precision select a lower dyadic slope and "
                + "its boundary bit."),
            Node("UpperOutput", "Slope, phase, precision, and position select an actual "
                + "upper dyadic mechanical bit."),
            Node("StableOutput", "Slope, phase, and position select both an integer floor "
                + "and an actual mechanical bit."),
            Node("lowerReadout", "Floor division constructs the lower dyadic slope; the "
                + "second component reads its mechanical bit at phase one minus the source slope."),
            Node("upperReadout", "Ceiling division constructs the upper dyadic slope "
                + "before reading the mechanical bit at the supplied phase and position."),
            Node("stableReadout", "The same slope and phase supply the cumulative "
                + "floor and the mechanical bit at the selected position."),
            Node("lowerArena", "For every irrational slope strictly between zero and one "
                + "and every precision, the law retains the nonnegative lower slope, its "
                + "positive error below the reciprocal power of two, the true source "
                + "boundary bit, and the false lower bit."),
            Node("upperArena", "For each slope, phase, and finite word length, the law "
                + "requires a precision after which every observed upper bit equals the "
                + "source bit."),
            Node("stableArena", "Without positive-time integer hits in the finite prefix, "
                + "the law requires a positive slope radius preserving every listed floor "
                + "and mechanical bit."),
            Node("lowerRealization", "The selected CUT readout is the complete lower "
                + "dyadic slope and boundary-bit function."),
            Node("upperRealization", "The selected CUT readout is the complete upper "
                + "dyadic bit function."),
            Node("stableRealization", "The selected CUT readout is the joint floor and "
                + "mechanical-bit function."))));

    private static DocumentBlock.Describe Node(string declaration, string text) =>
        Describe.Lean(
            DescribeId.Create("mechanical-dyadic-" + declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration),
            H(declaration),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            DescribeRole.Definition);
}
