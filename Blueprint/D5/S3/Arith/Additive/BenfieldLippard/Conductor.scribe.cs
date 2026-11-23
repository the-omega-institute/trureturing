using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive.BenfieldLippard;

internal sealed class ConductorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Additive/BenfieldLippard/Conductor.";
    private static readonly LibraryNoteRef Paper =
        LibraryNoteRef.Create("D5/L/Semigroups/benfieldlippard2025positivepowers");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive generator and bounded coprime shifts give an explicit cutoff for their additive closure.",
        H("A conductor from bounded generators"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("conductor"),
                DeclarationHandle.Create(Prefix + "bounded_conductor"),
                H("A conductor from bounded generators"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Paper),
                Blocks(Paragraph(Text(
                    "Starting from zero modulo the chosen generator A, the sets of attained residues grow strictly in each step until all residues are attained. At most A−1 steps of weight at most W suffice, after which adding A reaches every natural number at least (A−1)W."))),
                DescribeRole.Theorem)
        )));
}
