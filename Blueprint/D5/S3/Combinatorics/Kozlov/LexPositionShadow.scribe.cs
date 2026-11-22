using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Kozlov;

internal sealed class LexPositionShadowDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Convexity/snellman2026kozlov");
    private const string Prefix = "D5/S3/Combinatorics/Kozlov/LexPositionShadow.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Position-first compression fills earlier components before later ones. Its upper shadow has the same position-first shape at the next degree.",
        H("Position-first lex segments and shadow nesting"),
        Blocks(
            Node("greedyshape", "GreedyShape", "The shape of a left-filled allocation", DescribeRole.Definition,
                "After a component has less than its capacity, every later component has size zero."),
            Node("greedyshape-greedy", "greedyShape_greedy", "The greedy allocation is left-filled", DescribeRole.Lemma,
                "If the first component is underfull the residual is zero. Otherwise recurse on that residual."),
            Node("eq-greedy", "eq_greedy", "A left-filled allocation is determined by its total", DescribeRole.Lemma,
                "At each position its size is the lesser of the remaining total and that component's capacity."),
            Node("greedy-mono", "greedy_mono", "Greedy allocations grow componentwise", DescribeRole.Lemma,
                "Both the head allocation and its residual are monotone in the requested total. Induct on the list."),
            Node("tailcap", "tailCap", "Capacity of a component suffix", DescribeRole.Definition,
                "Discard the prescribed number of initial components and sum the remaining capacities."),
            Node("tailcap-zero", "tailCap_zero", "The full capacity", DescribeRole.Lemma,
                "Discarding zero components leaves the entire capacity sum."),
            Node("costz-zero", "costZ_zero", "The empty component costs zero", DescribeRole.Lemma,
                "Its shadow has size zero in either degree case."),
            Node("sig-le-choose-succ", "sig_le_choose_succ", "A shadow fits in the next layer", DescribeRole.Lemma,
                "Use the recursive count and compare with the full layer."),
            Node("capz-succ-of-nonneg", "capZ_succ_of_nonneg", "Capacity at the successor degree", DescribeRole.Lemma,
                "For a nonnegative degree the successor capacity is the corresponding successor binomial coefficient."),
            Node("costz-le-capz-succ", "costZ_le_capZ_succ", "The shadow fits in the successor capacity", DescribeRole.Lemma,
                "Use the shadow bound for nonnegative degrees and the empty component otherwise."),
            Node("costz-capz", "costZ_capZ", "A full nonnegative component has full shadow", DescribeRole.Lemma,
                "Apply the full-layer identity to the integer degree."),
            Node("cost-pos", "cost_pos", "A positive total cost has a positive component", DescribeRole.Lemma,
                "The summed nonnegative costs are positive only when a component contributes."),
            Node("greedyshape-shadow", "greedyShape_shadow", "Shadow sizes are still left-filled", DescribeRole.Lemma,
                "A full nonnegative component shadows to full capacity. The ordered degrees and zero-cost tails preserve the greedy shape, including negative and terminal degrees."),
            Node("islexfseg", "IsLexFSeg", "Position-first segments of a specified mass", DescribeRole.Definition,
                "Use lex-initial components with the sizes obtained by greedy allocation for the degree list and total."),
            Node("exists-islexfseg", "exists_isLexFSeg", "Existence of position-first segments", DescribeRole.Theorem,
                "Realize each greedy size by an initial segment in that degree."),
            Node("card-sum", "card_sum", "Total cardinality of a position-first segment", DescribeRole.Lemma,
                "Its allocated sizes sum to the minimum of its requested mass and the full capacity."),
            Node("resize", "resize", "Read the segment at its attained mass", DescribeRole.Lemma,
                "The same greedy sizes are recovered when the requested mass is replaced by their total."),
            Node("islexinit-subset-of-card-le", "isLexInit_subset_of_card_le", "Initial segments are nested by size", DescribeRole.Lemma,
                "If a face of the smaller initial segment were missing from the larger one, initiality forces the reverse inclusion and a cardinality contradiction."),
            Node("forall2-subset-of-le", "forall2_subset_of_le", "Compare the components of two lex lists", DescribeRole.Lemma,
                "Match components at equal degrees and apply nesting to each cardinality comparison."),
            Node("forall2-subset", "forall2_subset", "Position-first nesting", DescribeRole.Theorem,
                "Greedy monotonicity supplies the componentwise inequalities and initiality supplies inclusion."),
            Node("islexfinitial", "IsLexFInitial", "Position-first initial families", DescribeRole.Definition,
                "Each component is lex-initial and a nonempty later component forces all earlier components to be full."),
            Node("islexfinitial-cons-iff", "isLexFInitial_cons_iff", "Peel off the first component", DescribeRole.Lemma,
                "The head is initial, the tail is position-first initial, and a nonempty tail requires a full head."),
            Node("exists-getd-nonempty-iff", "exists_getD_nonempty_iff", "Nonempty components and list indexing", DescribeRole.Lemma,
                "A nonempty indexed component belongs to an actual list position and conversely."),
            Node("full-iff", "full_iff", "A component attains capacity exactly when full", DescribeRole.Lemma,
                "Apply uniform-layer inclusion and finite cardinality. Negative degrees have only the empty component."),
            Node("islexfinitial-iff-shape", "isLexFInitial_iff_shape", "Position-first initiality as a cardinal allocation rule", DescribeRole.Lemma,
                "Use the initiality criterion at the head to equate fullness with capacity and recurse along the list."),
            Node("islexfinitial-iff", "isLexFInitial_iff", "Characterize position-first segments by their total", DescribeRole.Theorem,
                "Identify a left-filled size list with the greedy allocation at its actual total."),
            Node("component-lexinit-upshadow", "component_lexInit_upShadow", "Move one initial component to the successor degree", DescribeRole.Lemma,
                "The shadow of a nonnegative lex segment has the specified size and is initial. The empty negative component also remains admissible."),
            Node("shadow-card", "shadow_card", "Size of a shadow component", DescribeRole.Lemma,
                "Apply the recursive shadow cardinality to each component of the position-first segment."),
            Node("shadow-sum", "shadow_sum", "Total upper-shadow size", DescribeRole.Lemma,
                "Sum the component cardinalities to read the total as the greedy shadow cost."),
            Node("lem-lexf-shadow", "lem_lexF_shadow", "The position-first shadow", DescribeRole.Theorem,
                "Combine component initiality with the left-filled shape of the shadow sizes."),
            Node("lem-lexf-shadow-subset", "lem_lexF_shadow_subset", "Shadow nesting in the next degree", DescribeRole.Theorem,
                "If the shadow's mass is bounded by the next segment size, compare the position-first allocations and use nesting componentwise."))));

    private static DocumentBlock Node(string id, string name, string title, DescribeRole role, string prose, Formula? formula = null) =>
        Describe.Lean(DescribeId.Create("kozlov-lex-position-shadow-" + id),
            DeclarationHandle.Create(Prefix + name), H(title),
            formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(formula),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
