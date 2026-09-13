using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class InclusionRegistrationsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact inclusion registration programs over finite supports.",
        H("InclusionRegistrations"),
        Blocks(
            Node("eightArena", "The object states are exactly the union of inherited period-eight Golden codes and period-seven Golden codes.", DescribeRole.Definition),
            Node("eightRealization", "The readouts retain membership in inherited period-eight Golden codes and period-seven Golden codes.", DescribeRole.Definition),
            Node("eightFirst", "An explicit code in the finite support witnesses an inhabited arena.", DescribeRole.Definition),
            Node("eightSecond", "A second distinct supported code witnesses that no padding states are needed.", DescribeRole.Definition),
            Node("eight_bridge", "The finite-support bridge preserves the original inclusion statement without using the source theorem.", DescribeRole.Theorem),
            Node("eight_lawSensitive", "The frozen source theorem satisfies the law; true source admission and false target admission falsify it.", DescribeRole.Theorem),
            Node("eight_slotSensitive", "The shared template supplies checked sensitivity of both ADMIT slots.", DescribeRole.Theorem),
            Node("nineArena", "The object states are exactly the union of inherited period-nine Golden codes and period-eight Golden codes.", DescribeRole.Definition),
            Node("nineRealization", "The readouts retain membership in inherited period-nine Golden codes and period-eight Golden codes.", DescribeRole.Definition),
            Node("nineFirst", "An explicit code in the finite support witnesses an inhabited arena.", DescribeRole.Definition),
            Node("nineSecond", "A second distinct supported code witnesses that no padding states are needed.", DescribeRole.Definition),
            Node("nine_bridge", "The finite-support bridge preserves the original inclusion statement without using the source theorem.", DescribeRole.Theorem),
            Node("nine_lawSensitive", "The frozen source theorem satisfies the law; true source admission and false target admission falsify it.", DescribeRole.Theorem),
            Node("nine_slotSensitive", "The shared template supplies checked sensitivity of both ADMIT slots.", DescribeRole.Theorem),
            Node("sixArena", "The object states are exactly the union of inherited period-six Tribonacci codes and period-five Tribonacci codes.", DescribeRole.Definition),
            Node("sixRealization", "The readouts retain membership in inherited period-six Tribonacci codes and period-five Tribonacci codes.", DescribeRole.Definition),
            Node("sixFirst", "An explicit code in the finite support witnesses an inhabited arena.", DescribeRole.Definition),
            Node("sixSecond", "A second distinct supported code witnesses that no padding states are needed.", DescribeRole.Definition),
            Node("six_bridge", "The finite-support bridge preserves the original inclusion statement without using the source theorem.", DescribeRole.Theorem),
            Node("six_lawSensitive", "The frozen source theorem satisfies the law; true source admission and false target admission falsify it.", DescribeRole.Theorem),
            Node("six_slotSensitive", "The shared template supplies checked sensitivity of both ADMIT slots.", DescribeRole.Theorem))));

    private static DocumentBlock.Describe Node(string declaration, string text, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/InformationEscape/InclusionRegistrations." + declaration),
            H(declaration),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            role);
}
