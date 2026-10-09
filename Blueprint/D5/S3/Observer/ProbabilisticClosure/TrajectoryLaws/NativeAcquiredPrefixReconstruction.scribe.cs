using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class NativeAcquiredPrefixReconstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixReconstruction.";

    public DocumentDefinition Create()
    {
        Formula nf = F.Id("nf"), op = F.Id("op"), ops = F.Id("ops");
        Formula form = F.Id("PrefixForm"), word = Call("List", F.Id("Operation"));
        Formula reconstructed = Call("reconstruct", nf);
        Formula run = Equal(Call("run", ops), Call("some", reconstructed));
        Formula facts = Call("PrefixFacts", nf, reconstructed);
        Formula finite = Equal(Call("finiteRun", ops), Call("some", Call("pi", reconstructed)));
        Formula matching = Equal(Call("render", nf), ops);
        Formula unique = Seq(Exists, Bang, Sp, nf, Colon, form, Comma, Sp, matching);
        Formula earning = All("ops", word, Seq(
            Open, Call("Legal", ops), Leftrightarrow, Open, unique, Close, Close, Land,
            All("nf", form, Imp(matching, Seq(run, Land, facts, Land, finite)))));
        Formula step = All("nf", form, All("op", F.Id("Operation"),
            Equal(Call("nativeStep", reconstructed, op),
                Call("map", F.Id("reconstruct"), Call("appendForm", nf, op)))));
        Formula execution = All("nf", form,
            Equal(Call("run", Call("render", nf)), Call("some", reconstructed)));
        Formula invariant = All("nf", form, facts);

        return DocumentDefinition.Create(ScribeNode.Create(
            "Every legal initialized operation prefix reconstructs its unique full native state.",
            H("Complete acquired-prefix reconstruction"), Blocks(
                Paragraph(Text("run folds the literal partial nativeStep transactions from the single empty initialization. Legal(ops) means that this fold returns some state; failure is an illegal word, not a performed rejection action. PrefixForm and render are the independent concatenation grammar of ordered rejected pairs, accepted seed, completed segment words, active partial cuts, pending and delivered. reconstruct computes the original finite fields, unbounded S and acquired counts from a form. It is not the definition of execution.")),
                Node("reconstruct-append-form", "reconstruct_append_form", "The actual successor matches form extension", step,
                    "Map denotes Option.map. For every form and actual operation, folding one literal transaction from its calculated state agrees with extending the independent form and reconstructing the result. Structural induction follows every segment and each seed phase, including partial beta, fourth-segment returns and both terminal colors. Stop succeeds only at its matching pending cut."),
                Node("run-render", "run_render", "Every form executes from empty initialization", execution,
                    "Induction executes the rejected pairs in their specified order, then the actual accepted pair and each payload block. The unbounded native loop theorem accounts for every beta-alpha return with its numeric banks. Completing letters perform the original writers and the next control. Pending needs no operation; delivered executes the uniquely matching Stop. Both seeds, arbitrary retry orders, arbitrary natural return counts, empty and partial words are included."),
                Paragraph(Text("PrefixFacts specifies the exact earned state. At seed-ready the finite fields are seed none and emptyRegisters, S=0 and counts=(2p,2q), where p and q count rejected alpha-alpha and beta-beta pairs. A pending first seed letter changes only its control and its corresponding count. In an acquired payload form, let bs=completedBits, t=length(bs), w=markerWeight(bs), J=returns and e=pendingExponent. Then S=J, A=1+t-w+2p+J and B=1+2w+2q+J+e; subtraction in A is natural subtraction, with w at most t. The original completedCount is t.")),
                Paragraph(Text("The same predicate also states that Registers equals the original marker writer fold; WrittenFields gives the live seed, exact natural weight and syndrome, first-marker Z, QOne and QTwo held at bs.take(3), and the post-third bare snapshot held thereafter. The arbitrary-length total-writer invariant supplies these fields; the original four-slot bound makes the weight modulo five equal its natural sum. recoverMarkers of the actual finite fields equals bs.take(3), including both active phases and the pending or delivered terminal cut. SegmentRefinements states, for every completed segment, the existing first-completion Parses predicate on pWord(j,b), recursively for its remaining segments.")),
                Node("reconstruction-invariants", "reconstruction_invariants", "Exact S, counts and written fields", invariant,
                    "Induction over the independent payload form gives accumulated returns, the two paid-count equations, the original completed count and the actual writer fold. The arbitrary-length marker invariant supplies every seed and selected triple, including all-equal triples, the post-write latch and held records; the four-slot bound restores exact natural weight. Each local segment invokes the exact first-completion language theorem. At the third latch e=0 and t=3, so A=4-w+2p+J and B=1+2w+2q+J. No selected count bank or receiver delivery is assumed."),
                Node("native-acquired-prefix-reconstruction", "native_acquired_prefix_reconstruction", "The full native prefix theorem", earning,
                    "For every finite operation word ops, legality is equivalent to existence of exactly one rendered form. Every such form gives the actually folded full state and all PrefixFacts, while the independently folded finite table yields its finite projection pi(c)=c.source.finiteFields. For the forward implication, induction on right extension of a legal word obtains its form using the proved native successor identity. The independent decoder proves uniqueness. Conversely each form executes by the initialized-run theorem. A separate induction proves projection commutation through the entire fold."),
                Paragraph(Text("The finite fields share completed t and fixed-selector latch status with original control and snapshot: the theorem proves their original phase and writer invariants. The source keeps S and live counts even where the finite projection erases them. No retry order or marker word is a runtime archive, and no numeric bank is newly delivered by Stop. This finite-prefix theorem does not identify initialized and resumed measurable future laws. Full infinite continuations, raw/event measurable inverses, shared-depth conditioning, posterior mixtures and the subsequent coherence and rank conclusions require further results.")))));
    }
    private static DocumentBlock.Describe Node(string id, string declaration, string title,
        Formula statement, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula Seq(params Formula[] xs) => F.Seq(xs);
    private static Formula All(string x, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(x), Colon, type, Comma, Sp, Open, body, Close);
    private static Formula Imp(Formula premise, Formula body) =>
        Seq(Open, premise, Close, Rightarrow, Open, body, Close);
    private static Formula Equal(Formula x, Formula y) => Seq(x, Eq, y);
    private static Formula Call(string name, params Formula[] xs)
    {
        var parts = new Formula[xs.Length * 2 - 1];
        for (var i = 0; i < xs.Length; i++)
        {
            parts[i * 2] = xs[i];
            if (i > 0) parts[i * 2 - 1] = Comma;
        }
        return Seq(Operatorname, Grp(F.Id(name)), Open, Seq(parts), Close);
    }
}
