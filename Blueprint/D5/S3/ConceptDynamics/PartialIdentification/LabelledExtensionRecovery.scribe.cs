using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.PartialIdentification;

internal sealed class LabelledExtensionRecoveryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A complete label history identifies its event order exactly when every label fiber " +
        "is a chain in the finite induced partial order.",
        H("Recovering Event Order from Labels"),
        Blocks(
            Paragraph(Text(
                "Let E be any partially ordered type, A any alphabet, F any finite subset of E, " +
                "and label a function from E to A. The two types have independent universes and " +
                "may be empty or infinite. A complete extension has no repeated event, contains " +
                "exactly F, and never places a predecessor after its successor. The order is " +
                "the order induced on F. An arbitrary F need not be a lower set of E, so these " +
                "lists do not assert global execution in the ambient event system.")),
            Describe.Lean(
                DescribeId.Create("labelled-extension-recovery"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/PartialIdentification/LabelledExtensionRecovery.result"),
                H("Exact classification of label recovery"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Every two equal-labelled events in F are comparable if and only if any " +
                        "two complete extensions with the same label list are equal as event lists. " +
                        "Repeated labels are allowed, and neither a finite alphabet nor a finite " +
                        "ambient event type is assumed. The empty support is included.")),
                    Paragraph(Text(
                        "For reconstruction, compare the first events of two extensions. Their " +
                        "labels agree. If they were distinct, each would occur in the other tail. " +
                        "The two extension conditions would then forbid both comparison directions, " +
                        "contradicting the chain condition on that label fiber. The heads agree, " +
                        "and recursion recovers the remaining events.")),
                    Paragraph(Text(
                        "For the obstruction, take incomparable events with the same label. In the " +
                        "finite subtype of F, the union of their strict predecessor sets is a lower " +
                        "cut containing neither event. The existing finite-poset extension theorem " +
                        "supplies a prefix ending at this cut and a suffix after both events. " +
                        "Concatenating extension lists gives both adjacent orders with a shared " +
                        "prefix and suffix. They have the same label word and distinct event orders. " +
                        "The proof transports exact support, no repetitions, and the pairwise order " +
                        "condition between subtype lists and ambient lists.")),
                    Paragraph(Text(
                        "This is a repository-derived classification with classical nice-labelling " +
                        "context; it makes no originality claim. Nice labels in finite conflict-free " +
                        "event structures separate incomparable events, equivalently giving chain " +
                        "fibers. See Santocanale, arXiv:0903.3462v1, Definition 2.3, Lemma 2.11, " +
                        "and Proposition 2.12. The present statement concerns complete extensions " +
                        "of arbitrary finite induced subsets and an arbitrary alphabet."))),
                DescribeRole.Theorem))));
}
