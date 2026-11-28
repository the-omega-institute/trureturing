using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.QuadraticIdeals;

internal sealed class GoldenCubicPurePrimeResidueClockDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Factorization/QuadraticIdeals/GoldenCubicPurePrimeResidueClock.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At the inert golden primes, the actual residue algebras have no transient.",
        H("Pure residue clock of the actual cyclic cubic fields"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("wss-native-pure-prime-lucas-clock"),
                DeclarationHandle.Create(Module + "pure_clock_nonsplit_golden"),
                H("The signed Lucas coordinate is purely periodic and all blocks stay nonzero"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At primes congruent to one modulo three and with negative golden quadratic character, the "
                    + "golden unit has a return exponent coprime to three. Cubing therefore gives a return through "
                    + "all signed Lucas levels, and a zero block would contradict periodicity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("wss-native-pure-prime-residue-clock"),
                DeclarationHandle.Create(Module + "pure_native_residue_ring_clock"),
                H("The actual residue algebras repeat from the first level"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A single positive period makes the full rings of integers modulo the specified prime "
                    + "ring-isomorphic at the corresponding native field levels. The proof uses the exact conductor "
                    + "witness and Kummer-Dedekind at the two levels. No assertion about Chebotarev densities or "
                    + "the least period is included."))),
                DescribeRole.Theorem))));
}
