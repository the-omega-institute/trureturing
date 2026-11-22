using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class GoldenCubicScalarFrobeniusReadoutDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three scalar comparisons in the prime field recover the oriented native Cardano witness.",
        H("Scalar readout of the golden cubic"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-field-scalar-oriented-readout"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/GoldenCubicScalarFrobeniusReadout.prime_field_scalar_oriented_readout"),
                H("The signed prime-field recurrence reads all three orientations"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a prime q greater than three, let x be the prime-field parameter, B=x squared plus three nonzero, and A=2 times x squared minus six. Start the recurrence D with zero and one and use A and B squared as its sum and product parameters. Let m=(q-1)/3 in the split case and (q+1)/3 in the inert case. The recurring numerator 4xD_m equals zero or the positive or negative value B^m exactly at the corresponding oriented Cardano labels.")),
                    Paragraph(Text("The inert comparison uses the inverse of the degree-two residue-field witness and consumes the protected GoldenCubicInertFrobeniusReadout. The actual computations on the left take place in the prime field and do not require an extension element, square root or inverse. A root of minus three is assumed only on the right; its Frobenius sign is proved, not assumed.")),
                    Paragraph(Text("The divided-power identity is the classical second-kind Dickson identity (Bhargava and Zieve, Finite Fields and Their Applications 5, 1999). For oriented quadratic ratios at this exponent and Lucas congruences see Zhi-Hong Sun, Cubic residues and binary quadratic forms, Journal of Number Theory 124, 2007, DOI 10.1016/j.jnt.2006.08.001. The result here certifies the actual repository readout and its orientation, not a priority claim about the classical arithmetic.")),
                    Paragraph(Text("No global conductor correction, reciprocity theorem, polynomial fiber count, complexity bound or Wall-Sun-Sun settlement is asserted."))),
                DescribeRole.Theorem))));
}
