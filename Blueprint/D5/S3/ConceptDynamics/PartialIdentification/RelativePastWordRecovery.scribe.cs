using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.PartialIdentification;

internal sealed class RelativePastWordRecoveryDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/PartialIdentification/RelativePastWordRecovery.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "From any preloaded event set, labels determine every finite legal event word exactly " +
        "when equally labelled fresh events with finite strict past outside the preload are comparable.",
        H("Recovering Event Words from an Arbitrary Preload"),
        Blocks(
            Paragraph(Text(
                "Let E be a partially ordered type, A an alphabet, I a subset of E, and label a " +
                "function from E to A. The types E and A have independent universes. They may be " +
                "empty or infinite. The preload I is arbitrary: it need not be finite or a lower " +
                "set. Its members are already present before any event in the observed word is added.")),
            Paragraph(Text(
                "Enabled K e is the original EnabledPathSwapConnectivity predicate: e is absent " +
                "from K and every strict predecessor of e belongs to K. Its Exec K l J predicate " +
                "executes a finite list by successively inserting enabled events. For the empty " +
                "list it requires K = J; for a list with head e and tail t it requires Enabled K e " +
                "and Exec (insert e K) t J. Thus legality is checked at each actual intermediate " +
                "set, starting from the given preload.")),
            Describe.Lean(
                DescribeId.Create("relative-past-word-recovery"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Exact relative-past criterion for word recovery"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every I and label, the function sending l to l.val.map label on the " +
                        "subtype {l : List E // there exists J : Set E, Exec I l J} is injective " +
                        "if and only if the following condition holds. For all a and b in E, " +
                        "if a is absent from I, b is absent from I, both Set.Iio a outside I and " +
                        "Set.Iio b outside I are finite, and label a = label b, then a <= b or " +
                        "b <= a. Here Set.Iio e consists of the strict predecessors of e, and " +
                        "outside I means set difference. The endpoint J is existentially " +
                        "quantified separately for each word; words with different endpoints " +
                        "are compared by the same injectivity assertion.")),
                    Paragraph(Text(
                        "The criterion allows repeated labels along chains. It restricts only " +
                        "fresh events with finite remaining strict past, rather than requiring " +
                        "all strict pasts in E to be finite. There is no countability assumption, " +
                        "no uniform bound on these finite sets, and no finiteness assumption on " +
                        "the alphabet. Every word being compared is finite and may stop before " +
                        "exhausting the available events. Recovery concerns the ordered event " +
                        "list itself, including its length and every event at every position.")),
                    Paragraph(Text(
                        "To obtain the criterion from injectivity, suppose a and b are fresh, " +
                        "incomparable events with the same label and finite remaining pasts. " +
                        "Let S be the union of their strict predecessor sets outside I. This " +
                        "finite set is disjoint from I. Every strict predecessor of a member " +
                        "of S belongs either to I or to S, by transitivity of the original order. " +
                        "Apply EnabledPathSwapConnectivity.result to the finite induced order " +
                        "on S, from its empty set to its entire carrier. Lift the resulting " +
                        "execution to E, retaining I throughout: the intermediate sets become " +
                        "I union the subtype images of the intermediate residual sets. A " +
                        "predecessor already in I stays present, and every other required " +
                        "predecessor is supplied by that induced execution.")),
                    Paragraph(Text(
                        "This constructs a common actual prefix p ending at K = I union S. " +
                        "Incomparability ensures that neither a nor b belongs to S, and every " +
                        "strict predecessor of either event is in K. Both events are therefore " +
                        "enabled at this same K. The existing exec_append theorem gives the " +
                        "two legal words p followed by a and p followed by b. Their label words " +
                        "agree. Injectivity makes the event words equal, and cancellation of " +
                        "the common prefix forces a = b, contradicting incomparability. This " +
                        "argument uses actual legal continuations of one prefix and imposes " +
                        "no common final-set requirement.")),
                    Paragraph(Text(
                        "For the converse, take two executions from I with equal label words. " +
                        "The execution membership identity exec_data makes every event in " +
                        "either word fresh relative to I. The strict-predecessor induction " +
                        "exec_past_mem shows that every predecessor outside I occurs in the " +
                        "same finite word, so the criterion applies to any equally labelled " +
                        "pair drawn from these words. Compare their heads at a shared current " +
                        "set. If the heads were distinct, comparability would make one a " +
                        "strict predecessor of the other. Enabledness of the latter would " +
                        "put the former in the current set, contradicting its freshness. " +
                        "The heads agree; insert their common event and repeat on the tails. " +
                        "Equality of label lists also handles the empty-list cases. Induction " +
                        "therefore recovers the entire event word.")),
                    Paragraph(Text(
                        "When I is empty, the remaining strict past is the whole strict past, " +
                        "giving the empty-preload instance of the same statement. When every " +
                        "event is preloaded, the only executable word is empty and the " +
                        "fresh-event condition has no instances. Preloaded labels and the " +
                        "order in which preloaded events were acquired are not observations " +
                        "in this statement. The theorem requires no execution producing I " +
                        "from the empty set and no infinite continuation after a finite word.")),
                    Paragraph(Text(
                        "Santocanale, https://arxiv.org/html/0903.3462v1, Definition 2.3, defines " +
                        "nice labellings as finite-alphabet colorings separating orthogonal " +
                        "events in an event structure. Lemma 2.11 relates orthogonality cliques " +
                        "to distinct enabled extensions of a common configuration, and " +
                        "Proposition 2.12 relates these colorings to deterministic concurrent " +
                        "edge colorings. These results provide the event-structure context " +
                        "for the common-prefix obstruction. The statement here uses the " +
                        "original conflict-free partial-order execution predicates, an " +
                        "arbitrary alphabet and an arbitrary preloaded subset; the cited " +
                        "results are not asserted to supply that complete relative-past equivalence."))),
                DescribeRole.Theorem))));
}
