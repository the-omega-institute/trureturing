using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class GoldenCubicOrbitClosureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The native cubic Lucas orbit realizes the full profinite adding machine.",
        H("Full profinite adding machine of cubic Lucas blocks"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-cubic-native-adding-machine"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicOrbitClosure.nativeAddingMachine"),
                H("The actual omega-limit is homeomorphic to the profinite integers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The full positive-modulus time labels, with the product topology, "
                    + "parameterize the simultaneous residue limits of the actual native "
                    + "Lucas trajectory, bijectively and continuously in both directions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-native-adding-machine-step"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicOrbitClosure.nativeAddingMachine_next"),
                H("The cubic step is addition by one"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Advancing the profinite time by one is exactly the native cubic "
                    + "update followed by reduction at every observation coordinate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-native-isolated-reading"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicOrbitClosure.actualReading_open"),
                H("Every actual forward reading is isolated in the full closure"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "One three-adic cylinder separates an actual reading from every "
                    + "different point of the full closure. All omega-limit tuples "
                    + "nevertheless have ternary coordinate one."))),
                DescribeRole.Theorem))));
}
