using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformSpecialDivisorExclusionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformSpecialDivisorExclusion";
    private const string Title = "A surviving cofactor on both special divisors";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformspecialdivisorexclusion-exists-ambientnativecofactor-not-mem-pullback"),
                DeclarationHandle.Create(Module + ".exists_ambientNativeCofactor_not_mem_pullback"),
                H("A surviving cofactor on both special divisors"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every suffix length at least five one of the ten exact ambient native cofactors avoids the pullback ideal for each of the zero-root and repeated-root loci."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodicmpsuniformspecialdivisorexclusion-nativecofactor-prime-avoids-special-equations"),
                DeclarationHandle.Create(Module + ".nativeCofactor_prime_avoids_special_equations"),
                H("Height-one prime exclusion on the special divisors"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A height-one prime containing the exact native cofactor ideal on the basic guard open contains neither spectral equation. The pulled-back reduced divisor ideals have height one and a native cofactor survives on each."))),
                DescribeRole.Theorem))));
}
