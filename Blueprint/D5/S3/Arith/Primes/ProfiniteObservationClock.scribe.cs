using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class ProfiniteObservationClockDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Arith/Primes/ProfiniteObservationClock";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact eventual collisions and period cofinality recover every absolute time label.",
        H("Profinite clocks from eventual observations"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("profinite-observation-finite-labels"),
                DeclarationHandle.Create(Module + ".finiteClock"),
                H("Exact finite absolute labels"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Equality at sufficiently late observations is exactly congruence modulo the period. "
                    + "Labeling an eventual state by the original observation index gives a bijection with the finite clock."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("profinite-observation-cofinal-equivalence"),
                DeclarationHandle.Create(Module + ".cofinalClock"),
                H("Cofinal periods recover the full clock"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A common refinement makes reduction from any sufficiently divisible observation period independent of choice. "
                    + "This reconstructs all compatible time labels, not only those from natural indices."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("profinite-observation-adding-machine"),
                DeclarationHandle.Create(Module + ".cofinalClock_next"),
                H("Advancement is addition by one"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The equivalence carries translation by one to the inverse-limit shift. "
                    + "The generic shift is invertible and agrees with a native recurrence on each observed coordinate."))),
                DescribeRole.Theorem))));
}
