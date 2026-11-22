using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformSpecialSpectralBasesDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformSpecialSpectralBases";
    private const string Title = "The reduced repeated-root equation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformspecialspectralbases-repeatedroot-vanishingideal-eq-radical"),
                DeclarationHandle.Create(Module + ".repeatedRoot_vanishingIdeal_eq_radical"),
                H("The reduced repeated-root equation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The vanishing ideal of the repeated-root locus is the radical of the principal discriminant ideal."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodicmpsuniformspecialspectralbases-rationalwitness-common-loci-and-minor"),
                DeclarationHandle.Create(Module + ".rationalWitness_common_loci_and_minor"),
                H("A witness in both special loci"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The literal rank witness belongs to the zero-root and repeated-root loci simultaneously."))),
                DescribeRole.Theorem))));
}
