using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Carry.OrderedGame;

internal sealed class CompletionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete ordered Long Game Strategy optimality with every permitted switch choice.",
        H("The Ordered Zeckendorf Long Game Strategy"),
        Blocks(
            Paragraph(Text("The source is Definition 1.6 and Conjecture 1.7 of Bortnovskyi "
                + "et al., The Ordered Zeckendorf Game, arXiv:2508.20222v2. Raw index zero "
                + "represents F1=1 and raw index one represents F2=2; decode maps successor. "
                + "The original Move, Preferred, LGSPath, Terminal and Conjecture17 definitions "
                + "are used unchanged. All adjacent inversion switches remain permitted, and "
                + "the strategy restarts priority after every move.")),
            Describe.Lean(DescribeId.Create("ordered-game-lgs-path-raw-erasure"),
                DeclarationHandle.Create("D5/S1/Digit/Carry/OrderedGame/Completion.lgs_path_raw_erasure"),
                H("Every ordered strategy path erases to a raw greedy path"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every LGSPath s t length weight, its raw multiplicities "
                    + "form a RawGreedyPath with the same weight. An available switch outranks "
                    + "every carry, so a selected carry starts sorted. In a sorted list each "
                    + "duplicate has an adjacent occurrence, and strict value order forces "
                    + "strict position order. Thus rightmost split selection excludes every "
                    + "higher duplicate. Absence of preferred splits makes a selected merge "
                    + "binary, and every lower enabled consecutive pair occurs to its left. "
                    + "Switches preserve counts and contribute zero reward; induction erases "
                    + "them without imposing an order on their choices."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ordered-game-complete-lgs-exists"),
                DeclarationHandle.Create("D5/S1/Digit/Carry/OrderedGame/Completion.complete_lgs_exists"),
                H("Finite complete LGS continuations exist from every ordered state"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every list has an actual finite LGS path ending at an "
                    + "ordered terminal state. At a nonterminal list, minimizing a natural rank "
                    + "over legal moves gives a move satisfying the exact relational priority. "
                    + "The rank uses priority first and the prescribed positional tie rule; "
                    + "all switches share the same rank. Carries strictly decrease the existing "
                    + "lexicographic token-count and index-weight measure, while switches "
                    + "preserve that measure and decrease inversions. Well-founded recursion "
                    + "on their combined measure gives completion. The empty and singleton "
                    + "states are included; in particular the source start n=1 is covered."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ordered-game-conjecture17-result"),
                DeclarationHandle.Create("D5/S1/Digit/Carry/OrderedGame/Completion.result"),
                H("Conjecture 1.7"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The conclusion is exactly Conjecture17. For every positive "
                    + "n there exists a complete LGS path from n ones. For every such complete "
                    + "LGS path, with every permitted switch choice retained, every arbitrary "
                    + "legal terminal competing path has at most its actual move count. "
                    + "The competitor's weight is at most G by raw_terminal_bound; the strategy's "
                    + "weight equals G by priority-preserving erasure and complete_greedy_reward. "
                    + "The exact strategy potential and the competitor potential bound turn "
                    + "these weight statements into the length comparison. Terminal inversion "
                    + "zero follows from the actual absence of switches, not from raw counts. "
                    + "No Bellman premise, deterministic-switch restriction or finite cutoff "
                    + "is added."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("ordered-zeckendorf-long-game-strategy"),
                    ResolutionKind.Proved)),
            Paragraph(Text("Source-fidelity and first-freeze admission remain subject to "
                + "independent review. Attribution remains with Bortnovskyi et al., Cusenza "
                + "et al., and the suppliers contributed in PRs 7495, 7575, 7643 and 7651. "
                + "This formal result makes no worldwide-priority claim.")))));
}
