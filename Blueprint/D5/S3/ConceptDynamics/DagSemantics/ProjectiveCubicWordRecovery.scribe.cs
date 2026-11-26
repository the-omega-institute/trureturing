using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DagSemantics;

internal sealed class ProjectiveCubicWordRecoveryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Consecutive ternary equality observers retain exactly the relative sign in each nonzero incidence run.",
        H("Projective recovery of cubic words"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("projective-cubic-word-recovery"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/DagSemantics/ProjectiveCubicWordRecovery.projective_cubic_word_recovery"),
                H("The exact collisions of consecutive ternary observers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For two words of any finite length over the three-element field, compare all entry-equality tests at distance one or two. The tests coincide if and only if their signed path differences differ by an independent sign on each run of nonzero differences. Zero differences separate the runs. Adjacent squared differences detect support, and the squared two-step difference detects the product of two consecutive nonzero differences.")),
                    Paragraph(Text("This is an exact finite-word fibre statement. It supplies the collision analysis for local equality observations of oriented cubic probe words. The formal statement does not assert a distribution over primes or compatible starting points, nor a statement about the physical faces of a random graph embedding."))),
                DescribeRole.Theorem))));
}
