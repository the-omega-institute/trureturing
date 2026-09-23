using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class GuardedEqualityRegistrationsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Guarded equality registration programs over complete finite object arenas.",
        H("GuardedEqualityRegistrations"),
        Blocks(
            Node("modelXYCode", "The shared constructor-written zero in Fin 3 is definitionally M_XY.", DescribeRole.Definition),
            Node("positiveFirstReadout", "Pinned finite equality with modelXYCode gives the original E_X guard on all three models.", DescribeRole.Definition),
            Node("positiveFirstArena", "All three candidate models remain in the arena.", DescribeRole.Definition),
            Node("positiveFirstRealization", "The explicit guarded template receives positiveFirstReadout, the model identity and constant modelXYCode, retaining the original guard and equality readouts.", DescribeRole.Definition),
            Node("positiveFirst_bridge", "Iff.rfl identifies the generated law with the original E_X hypothesis and model equality to M_XY.", DescribeRole.Theorem),
            Node("positiveFirst_lawSensitive", "The frozen theorem satisfies the law; changing the model readout falsifies it at M_XY while keeping E_X fixed.", DescribeRole.Theorem),
            Node("positiveFirst_slotSensitive", "The shared sensitivity theorem checks independent support for the guard and both equality slots.", DescribeRole.Theorem),
            Node("sourceZero", "The shared zero in Fin 6 codes outerH2.", DescribeRole.Definition),
            Node("sourceOne", "The shared one in Fin 6 codes outerH25.", DescribeRole.Definition),
            Node("dimension39Code", "Zero in Fin 2 codes the occurring dimension thirty-nine.", DescribeRole.Definition),
            Node("dimension40Code", "One in Fin 2 codes the occurring dimension forty and the right equality readout.", DescribeRole.Definition),
            Node("outerGuardReadout", "Boolean dispatch on finite equality recognizes exactly sourceZero and sourceOne as outer groups.", DescribeRole.Definition),
            Node("outerDimensionReadout", "Boolean dispatch selects dimension40Code for the two outer groups and dimension39Code for the four inner groups.", DescribeRole.Definition),
            Node("outerDimensionCodeArena", "Fin 6 re-coordinates all PhysicalSourceGroup states in order: outerH2, outerH25, oldInnerH2, oldInnerH25, newInnerH2, newInnerH25. The guarded equality outputs use Fin 2 dimension codes.", DescribeRole.Definition),
            Node("outerDimensionRealization", "The explicit guarded template uses the outer guard, the encoded dimension and constant dimension40Code on the full six-state arena.", DescribeRole.Definition),
            Node("outerDimension_bridge", "Local encode and decode maps form PhysicalSourceGroup ≃ Fin 6 via decodeEncode and encodeDecode. guardDecoded preserves the guard; dimensionEncoded matches the finite table. encodeDimension and decodeDimension reconstruct every occurring dimension and forty through dimensionDecoded, fortyEncoded and fortyDecoded. outputIff reflects equality of these codes to equality of dimensions, and pointwise transports the quantified conditional law. No injection from all natural numbers into Fin 2 is asserted.", DescribeRole.Theorem),
            Node("outerDimension_lawSensitive", "The frozen theorem satisfies the encoded law; replacing the dimension readout by zero falsifies it at source zero with its guard fixed. The conflicting output codes zero and one decode to thirty-nine and forty.", DescribeRole.Theorem),
            Node("outerDimension_slotSensitive", "The shared sensitivity theorem checks independent support for the guard and both equality slots.", DescribeRole.Theorem))));

    private static DocumentBlock.Describe Node(string declaration, string text, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations." + declaration),
            H(declaration),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            role);
}
