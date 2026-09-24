using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class MarkovPrefixMassDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Observer/tauceti2026markov");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Singleton prefix masses of a homogeneous Markov trajectory.",
        H("Singleton prefix masses of a homogeneous Markov trajectory"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("tauceti2026markov"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkovPrefixMass.markov_chain_law_map_prefix_apply_singleton"),
                H("Singleton prefix masses of a homogeneous Markov trajectory"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every measurable state space with measurable singletons, probability initial law, Markov transition kernel and natural prefix length, the singleton prefix mass equals the initial singleton mass times the product of transition singleton masses.")),
                    Paragraph(Text("The statement uses Mathlib trajMeasure directly with the homogeneous history-reading kernel. Prefix length is arbitrary, and zero initial or transition masses are permitted. The prefix extension preserves the current state and its transition kernel."))),
                DescribeRole.Theorem))));
}
