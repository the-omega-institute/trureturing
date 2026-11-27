using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class PeriodicMPSUniformOrderedCoverLiftDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformOrderedCoverLift";
    private const string Title = "The common-divisor lift to the ordered cover";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformorderedcoverlift-exists-horizontal-heightone-of-basicguard"),
                DeclarationHandle.Create(Module + ".exists_horizontal_heightOne_of_basicGuard"),
                H("The common-divisor lift to the ordered cover"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An irreducible native common divisor surviving the basic guard lifts to a height-one prime containing all ordered cofactors. Its contraction to native coordinates is the divisor ideal and its contraction to the homogeneous root ring is zero."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodicmpsuniformorderedcoverlift-native-commondivisor-dvd-basicguard-of-no-horizontal"),
                DeclarationHandle.Create(Module + ".native_commonDivisor_dvd_basicGuard_of_no_horizontal"),
                H("The basic guard contains every common divisor under horizontal exclusion"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume that no height-one prime of the ordered chart has zero root-ring contraction and contains every ordered cofactor. Then every irreducible native common cofactor divisor divides the basic guard in native coordinates."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodicmpsuniformorderedcoverlift-dimh-guarded-criticalcoordinates-le-of-no-horizontal"),
                DeclarationHandle.Create(Module + ".dimH_guarded_criticalCoordinates_le_of_no_horizontal"),
                H("Guarded critical dimension under horizontal exclusion"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the same ordered-prime exclusion at the given suffix length, the critical set of the actual normalized observation has Hausdorff dimension at most six on the nonzero mixed-trace and basic guard open."))),
                DescribeRole.Theorem))));
}
