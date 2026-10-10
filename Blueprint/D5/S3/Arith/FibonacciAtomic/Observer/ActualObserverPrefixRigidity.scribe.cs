using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class ActualObserverPrefixRigidityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverPrefixRigidity.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A truthful persistent raw cache lets one immutable source replay another actual prefix. A terminating continuation makes the raw history unique at the complete row.",
        H("Native Actual Prefix Replay and Rigidity"),
        Blocks(
            Paragraph(Text("E is an arbitrary finite nominal carrier and M is the original Observer on E. Histories retain literal addresses, chronological four-valued responses and repetitions. The initial row is common to sources. ActualPrefix extends a query row only, using its literal address and queryReply of the decoded ordered cache. This is distinct from arbitrary counterfactual response folds and from Run suffixes starting at different rows.")),
            Theorem("actualPrefix_replay", "Cross-source actual-prefix replay", "For every M and immutable sources U,V, every state e and raw history h, ActualPrefix(M,U,e,h) and readout(q,V)=readout(q,U) at every q in paid(h) imply ActualPrefix(M,V,e,h). There is no Legal, correctness, budget or termination assumption. Induction retains each complete row. A stored hit is identical on both sources; a miss uses the assumed raw readout equality. Branch and absent are never identified."),
            Theorem("actualPrefix_history_rigid", "Shared complete state determines the actual raw history", "For every M,U,V, assume Legal(M,U), ActualPrefix(M,U,e,h), ActualPrefix(M,V,e,hprime), CacheTruth(decoder(M,e),V), and Run(M,V,e0(M),t,f,b). Then h=hprime. Only V needs a terminating run; U needs legality but no separately supplied terminal run. The conclusion identifies histories, not sources. It does not assert decoder injectivity or uniqueness of arbitrary different-start suffixes."),
            Paragraph(Text("The original prefix_cache_spectrum puts every paid prefix address in the common cache. Its truth for U and V gives raw source agreement at those addresses. Prefix replay transfers h to V. The original prefix_run_tail splits the same terminating V-run after h and hprime, and run_deterministic equates the continuations. List right cancellation then equates the prefixes. Nonterminating repeated-query loops are outside the theorem. Wrong-address and post-halt counterfactual histories are outside ActualPrefix.")),
            Paragraph(Text("These are repository-derived native results, using the original cache-spectrum and prefix-tail suppliers. Generic deterministic-run, fold and list cancellation results alone do not supply the cross-source persistent-cache bridge. No runtime history port or additional nominal row is introduced."))
        )));
    private static DocumentBlock Theorem(string n, string title, string prose) => Describe.Lean(
        DescribeId.Create("actual-observer-prefix-rigidity-" + n.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + n), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
