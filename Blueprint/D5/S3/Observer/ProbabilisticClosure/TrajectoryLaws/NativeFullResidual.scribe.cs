using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class NativeFullResidualDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeFullResidual.";

    public DocumentDefinition Create()
    {
        Formula c = F.Id("c"), d = F.Id("d"), w = F.Id("omega"), n = F.Id("n");
        Formula k = F.Id("k"), ops = F.Id("ops"), op = F.Id("op"), s = F.Id("s");
        Formula t = F.Id("t"), p = F.Id("P"), q = F.Id("Q");
        Formula blocks = Call("eventBlocks", Fields(c), ops);
        Formula replay = Call("foldl", F.Id("replayBlock"), Fields(c), blocks);
        Formula trace = Call("fullTranscript", c, w);
        Formula active = Equal(Call("control", Fields(c)), Call("fourthActive", s));
        Formula reconstruction = Imp(Equal(Call("nativeDrive", c, w, n),
            Call("some", Tuple(ops, d, k))), And(
            Equal(Call("at", trace, n), Call("some", Tuple(ops, Fields(d), blocks))),
            And(Equal(replay, Fields(d)),
                Equal(Call("originalView", replay), Call("originalView", Fields(d))))));
        reconstruction = All(reconstruction, ("c", "AcquiredNativeState"),
            ("d", "AcquiredNativeState"), ("omega", "Stream"), ("n", "Nat"),
            ("k", "Nat"), ("ops", "ListOperation"));
        Formula deletion = All(Imp(Equal(Call("nextNative", c, w),
            Call("some", Tuple(op, d))), Equal(Call("deleteBlock", trace),
            Call("fullTranscript", d, Call("rawTail", w, Call("readCost", op))))),
            ("c", "AcquiredNativeState"), ("d", "AcquiredNativeState"),
            ("omega", "Stream"), ("op", "Operation"));
        Formula paths = All(Imp(active, Equal(trace, Call("fullTranscript", c,
            Call("tailStream", s, Call("stoppedReadWord", s, w))))),
            ("c", "AcquiredNativeState"), ("s", "ActivePhase"), ("omega", "Stream"));
        Formula inverse = All(Imp(active, All(Imp(Call("Valid", s, t),
            Equal(Call("readbackRaw", Call("fullRenderer", c, s, Call("validPair", t))), t)),
            ("t", "RawTail"))), ("c", "AcquiredNativeState"), ("s", "ActivePhase"));
        Formula tv = All(Imp(active, Equal(Call("TV", Call("map", p, Call("fullRenderer", c, s)),
            Call("map", q, Call("fullRenderer", c, s))), Call("TV", p, q))),
            ("c", "AcquiredNativeState"), ("s", "ActivePhase"),
            ("P", "MeasureValidTail"), ("Q", "MeasureValidTail"));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Full original residual rendering and event deletion.", H("Native full event space"), Blocks(
                Paragraph(Text("FiniteFields and its original writers come from NativeAcquiredPrefixState. Its control is the paid seed parser, early segment count and phase, fourth active phase, matching pending Stop or delivered Stop. Registers retain seed, live weight and syndrome, both ordered Q-plus records, first-marker Z and the held third snapshot. The snapshot stores seed, weight and syndrome; its ell and completed count are the fixed values 2 and 3. originalView supplies these constants, the fixed four-slot selector, the selected markers recovered from the written registers, marker-written and latch flags, and the exact partial finiteStep permission menu. No paid count, return counter, posterior or archive enters the rendered fields.")),
                Paragraph(Text("OriginalEvent is generated from the old fields. Every Read is retained. Seed pairs either reject and return to ready, or acquire their first letter as the seed. Payload p completes zero on alpha and suspends on beta; suspension returns on alpha and completes one on beta. A completion records its index and bit, writes live arithmetic and the original ordinal records, then performs the third latch when its old index is two. beforeLatch restores the old snapshot in the post-write event; only latched installs the new snapshot. The fourth write changes live arithmetic while Q-plus, Z and snapshot hold. Matching Stop records its bit and enters delivered. Illegal operations have no native successor.")),
                Paragraph(Text("FullTranscript is a measurable sequence of prefix cuts. A successful cut contains its complete operation prefix, full native finite fields and the ordered list of whole original event blocks. Initial fields are retained at cut zero. FullOutput has the discrete measurable structure; FullTranscript has the product structure. ListOperation means List Operation; tuple and at denote the displayed product and evaluation. fields(c) means c.source.finiteFields. replayBlock folds the individual written, latched, moved and held events over the old finite fields. originalView is determined by those fields, rather than an additional observer state.")),
                Node("full-event-reconstruction", "full_event_reconstruction", "Lawful event reconstruction",
                    reconstruction, "For every successful native prefix, replay of all actual event blocks reconstructs its fields and the original field view, including permissions. Induction over the executed operations uses the literal seed, payload and Stop cases. This statement applies to every initial native state and every lawful stream prefix, with no bound on paid returns."),
                Node("full-delete-block", "full_delete_block", "Delete one complete original block", deletion,
                    "deleteBlock shifts the prefix index by one, deletes the first operation and deletes the first whole event block. It retains the successor fields. Read shifts the source by one; Stop has readCost zero. Native resumption and finite projection prove equality with the successor transcript. No operation is removed without its deterministic block."),
                Paragraph(Text("ValidTail(s) is the subtype of RawTail whose finite elements are precisely some w with a WordFamily(s,b,w) witness for a bit b. It also contains none, representing the unique infinite noncompletion word. tailStream uses wordStream on finite words and infiniteTail on none. Thus the carrier retains every legal finite completion word and the old synthetic noncompletion possibility. At suspension, the already acquired beta is absent from future Reads.")),
                Node("full-renderer-all-paths", "full_renderer_all_paths", "Every raw path has its full representative",
                    paths, "For active native fourth control, every source stream renders identically to its stopped word representative. The noncompletion case is the unique infinite word, with all its prefix fields and blocks. The finite case agrees at every acquired prefix, its completion, matching Stop and every later failed cut."),
                Node("full-renderer-readback", "full_renderer_readback", "Full rendering has measurable readback",
                    inverse, "validPair(t) is t with its Valid proof. readbackRaw locates the unique delivered cut and reads back every Read letter there; if none exists it returns none. The delivered cut index is measurable by measurable first occurrence. The proof recovers exactly t on the lawful carrier. The auxiliary control projection is used only to locate delivery; it is not the rendered full law."),
                Node("full-renderer-tv", "full_renderer_tv", "Exact full-law total variation transport", tv,
                    "MeasureValidTail means Measure (ValidTail s). TV is canonical measurableTotalVariation, the ENNReal supremum of the two directed event gaps. Measurable rendering and its measurable left inverse give equality by the two map contractions. The statement holds for arbitrary measures on the lawful carrier, including measures with noncompletion mass. No half-l1 or real-valued convention is substituted."))));
    }

    private static DocumentBlock.Describe Node(string id, string declaration, string title,
        Formula statement, string prose) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula Fields(Formula c) => Call("fields", c);
    private static Formula And(Formula a, Formula b) => Seq(Open, a, Close, Land, Open, b, Close);
    private static Formula Imp(Formula a, Formula b) => Seq(Open, a, Close, Rightarrow, Open, b, Close);
    private static Formula Equal(Formula a, Formula b) => Seq(a, Eq, b);
    private static Formula Tuple(params Formula[] xs) => Call("tuple", xs);
    private static Formula All(Formula body, params (string Name, string Type)[] xs)
    {
        for (var i = xs.Length - 1; i >= 0; i--)
            body = Seq(Forall, Sp, F.Id(xs[i].Name), Colon, F.Id(xs[i].Type), Comma, Sp,
                Open, body, Close);
        return body;
    }
    private static Formula Seq(params Formula[] xs) => F.Seq(xs);
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
