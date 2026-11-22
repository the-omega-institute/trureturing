using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformHorizontalPrimeDescentDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformHorizontalPrimeDescent";
    private const string Title = "Horizontal height-one primes of the native cofactor ideal";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformhorizontalprimedescent-generic-prime-of-horizontal"),
                DeclarationHandle.Create(Module + ".generic_prime_of_horizontal"),
                H("A horizontal prime survives passage to the ordered-root fraction field"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The zero contraction to the ordered-root polynomial ring keeps all nonzero root coefficients out of the prime. The localization extends the prime, preserves its height, and contracts back to it."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodicmpsuniformhorizontalprimedescent-generic-torus-contraction-height"),
                DeclarationHandle.Create(Module + ".generic_torus_contraction_height"),
                H("The contraction to the parameter torus has height one"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite free monic quadratic tower gives going-down. Integral incomparability and the domain property give the lower bound on the contracted height."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodicmpsuniformhorizontalprimedescent-no-horizontal-prime"),
                DeclarationHandle.Create(Module + ".no_horizontal_prime"),
                H("Projected resultants exclude the exact ordered native cofactors"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Choose two of the ten native maximal minors on the ordered chart. If each generic image is a linear form in the two indicated radicals, multiplication by a partial conjugate gives a scalar contraction. If the cleared bivariate numerators have two nonzero projected resultants, no horizontal prime of height one contains all ten cofactors."))),
                DescribeRole.Theorem))));
}
