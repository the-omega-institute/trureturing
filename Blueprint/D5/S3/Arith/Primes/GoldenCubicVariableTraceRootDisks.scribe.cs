using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class GoldenCubicVariableTraceRootDisksDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Identify the primitive signed traces and exact same-prime root disks of the golden block with variable starting seed.",
        H("Variable golden trace and prime-power root disks"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-cubic-variable-trace-root-disks"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/GoldenCubicVariableTraceRootDisks.actual_variable_trace_root_disks"),
                H("Primitive signed-trace roots and exact same-prime contact"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Iterate the map x ↦ x³ + 3x from an arbitrary trace and add three to the square at the chosen level. At seed one, this is the protected golden Lucas block.")),
                    Paragraph(Text("An integral companion product gives the square root needed for the primitive signed-trace parameter in the original field. This gives exact Frobenius returns for each actual root in characteristics other than two and three.")),
                    Paragraph(Text("At every positive prime-power precision each residue root disk maps bijectively onto residues reducing to zero. Differences in the same root disk preserve divisibility by that same power of the prime.")),
                    Paragraph(Text("This identifies the exact same-prime precision of changes to a starting seed in an actual root disk. The seed-one specialization is not a proof that the Wall–Sun–Sun divisibility case cannot occur."))),
                DescribeRole.Theorem))));
}
