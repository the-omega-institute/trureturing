using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class ActualExactTraceCompilerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/ActualExactTraceCompiler.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Repeated logical requests retain full control history while raw caches use chronological first occurrences.",
        H("Exact Finite Trace Compiler"),
        Blocks(
            Paragraph(Text("The raw and coarse first-occurrence folds commute with kappa_hist. A repeated hit therefore keeps its stored raw branch or absent value, even for a contradictory supplied raw response. The exact carrier keeps every compatible cache lift over each first coarse history and one absorbing sink.")),
            Def("coarseCacheUpdate", "Coarse first-occurrence update", "A repeated logical address keeps its existing coarse value; a miss appends the new coarse report."),
            Def("firstRaw", "Raw first-occurrence fold", "The chronological cacheUpdate fold over a raw logical history."),
            Def("firstCoarse", "Coarse first-occurrence fold", "The corresponding chronological fold over coarse reports."),
            Def("exactRowDecoder", "Exact row decoder", "A compiler row decodes the compatible first-occurrence cache indexed by its full logical history."),
            Def("exactAppendRow", "Exact row extension", "A retained logical extension packs its updated raw cache into the extended first coarse fiber."),
            Def("exactAction", "Exact compiler action", "Control reads the full logical coarse history and the sink halts false."),
            Def("exactTransition", "Exact compiler transition", "A query extends the full history when retained and otherwise enters the absorbing sink."),
            Def("strategyPrefixes", "Strategy prefix carrier", "The finite union of all coarse prefixes of the original terminal traces over the allowed source domain."),
            Theorem("strategy_prefix_mem", "Original actual prefix belongs to the compiler carrier", "For every N, Strategy pi, allowed source U and raw history h prefixing terminal(pi,U).trace, kappa_hist(h) belongs to strategyPrefixes(N,pi). This preserves the original literal addresses, repetitions and coarse chronological order."),
            Def("strategyStateCard", "Strategy carrier cardinality", "The exact state count obtained from the strategy prefix carrier and compatible first-cache fibers."),
            Theorem("strategy_state_card", "Strategy state cardinality", "The strategy-indexed exact carrier has the stated finite cardinality."),
            Def("exactObserver", "Exact finite observer", "The finite carrier supplies an input-independent empty row, full-history coarse control and the first-occurrence raw decoder."),
            Def("ReplayStep", "Replay continuation contract", "Every requested extension from a specified original horizon prefix remains a retained coarse prefix and an original horizon prefix."),
            Def("ExactIndex", "Exact history index", "A finite carrier index for each retained coarse control history."),
            Def("ExactRow", "Exact cache row", "A control history paired with every compatible first-coarse raw cache lift."),
            Def("ExactState", "Exact state carrier", "The row carrier plus one absorbing unit sink."),
            Def("exactStateCard", "Exact cardinality expression", "The finite sum of compatible cache fiber cardinalities plus the sink."),
            Def("strategyPolicy", "Coarse strategy policy", "Evaluate the original strategy on the fixed coarse-history representative."),
            Describe.Lean(DescribeId.Create("actual-exact-trace-compiler-encode-projection"),
                DeclarationHandle.Create(Prefix + "encode_projection"), H("Exact coarse projection of the fixed section"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("g"), Colon, Sp, F.Id("CoarseHistory"), Comma, Sp,
                    new Formula.Apply(Seq(Operatorname, Grp(F.Id("kappaHist"))),
                        [new Formula.Apply(Seq(Operatorname, Grp(F.Id("encodeHistory"))), [F.Id("g")])]),
                    Sp, Eq, Sp, F.Id("g")))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every original coarse history g, kappa_hist(encodeHistory(g)) equals g. The section preserves each literal address and chronological repetition, chooses raw branch for coarse none, and chooses the corresponding raw Boolean leaf for a Boolean label. This is a right inverse of coarse projection, not an identity on arbitrary raw histories: branch and absent remain distinct raw replies. The native counterfactual completion obstruction consumes this exact supplier to certify its route representative."))),
                DescribeRole.Theorem),
            Def("strategyObserver", "Strategy-indexed observer", "Instantiate the exact finite observer on all allowed terminal coarse prefixes."),
            Paragraph(Text("Strategy-indexed replay, exact terminal runs and admissibility assume a positive source bound and an original strategy policy that factors through kappa_hist. Sourcewise replay and run statements range over the allowed sources at that bound.")),
            Theorem("strategy_actual_prefix_replay", "Strategy prefix cache replay", "Actual prefixes of the strategy-indexed observer carry the original full coarse history and first-write raw cache."),
            Def("exactControl", "Coarse control projection", "Forget cache lifts while retaining full logical coarse control or the sink."),
            Theorem("exact_all_history_factorization", "All-history ghost safety", "Equal coarse response histories have equal actions, including contradictory repeats and post-halt reports."),
            Theorem("strategy_exact_run", "Exact terminal run", "The compiled observer realizes the original terminal trace and output bit."),
            Theorem("strategy_admissible", "Finite observer admissibility", "The strategy-indexed observer satisfies the original bounded finite observer contract."),
            Theorem("strategy_state_card_bound", "Exact state bound", "A literal support and horizon bound controls the exact compatible-cache state count."),
            Paragraph(Text("The exact state count is one plus the sum of 2 to the number of distinct coarse-none addresses over retained full logical prefixes. The general bound uses the number of allowed sources, an explicitly supplied trace horizon and an explicitly supplied literal support. The route-specific horizon, original phase labels and minimum-price formulas are separate obligations."))
        )));
    private static DocumentBlock Def(string n, string title, string prose) => Describe.Lean(
        DescribeId.Create("actual-exact-trace-compiler-" + n.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + n),
        H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static DocumentBlock Theorem(string n, string title, string prose) => Describe.Lean(
        DescribeId.Create("actual-exact-trace-compiler-" + n.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + n),
        H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
