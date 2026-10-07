using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.ReturnWords;

internal sealed class CoherentReturnPathTemplatesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/ReturnWords/CoherentReturnPathTemplates.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Synchronized labelled returns characterize bounded component phases and give "
            + "a finite cover by multipower templates, with a two-loop obstruction to "
            + "finite single-power replacement.",
        H("Coherent returns, component phases and finite path-output templates"),
        Blocks(
            Paragraph(Text(
                "Vertices and output symbols are finite. Arrow types are unrestricted: "
                + "parallel arrows, loops and nondeterministic choices remain actual arrows. "
                + "Components are fibers of the native quotient by mutual directed reachability. "
                + "Output equality does not identify graph paths, arrows or separately observed "
                + "color histories. The template conclusion is a cover; arbitrary independent "
                + "exponent choices are not asserted to realize graph paths.")),
            Def("EdgeLabel", "Labels depend on actual arrows",
                "For vertex type V with a quiver and symbol type alpha, EdgeLabel V alpha "
                + "assigns a symbol to every arrow, with its source and target implicit. "
                + "No arrow type is assumed finite or subsingleton."),
            Def("output", "Outputs are native path weights",
                "For any actual Quiver.Path H, output label H is the list underlying "
                + "Path.weight in FreeMonoid alpha, where each arrow has singleton weight "
                + "FreeMonoid.of(label e). Empty paths output the empty word and every "
                + "arrow contributes exactly one symbol."),
            Def("Component", "The native SCC fiber",
                "For S in Quiver.StronglyConnectedComponent V, Component S consists of "
                + "vertices a whose native quotient class is S. Its quiver retains all "
                + "ambient arrows between its vertices."),
            Def("componentInclusion", "Inclusion preserves arrows",
                "The inclusion prefunctor sends a component vertex to its ambient vertex "
                + "and sends each actual internal arrow to that same ambient arrow."),
            Def("liftComponentPath", "Endpoint equality closes the whole path",
                "Given an ambient path H and proofs that both endpoints belong to S, "
                + "liftComponentPath returns an internal path whose image under the "
                + "inclusion prefunctor is exactly H. Native mutual reachability supplies "
                + "the closing path that puts each intermediate vertex in the same fiber. "
                + "The equality retains actual arrows, not just their output labels."),
            Def("componentLabel", "Restrict labels to the component",
                "componentLabel label S evaluates the original label on each actual "
                + "arrow of the component quiver."),
            Proof("component_inclusion_length", "Component inclusion preserves path length",
                "For every vertex type V, arbitrary quiver, strongly connected component S "
                + "and actual internal path H, the ambient image of H under componentInclusion S "
                + "has exactly the same length as H. No finiteness assumption is needed."),
            Proof("component_inclusion_output", "Component inclusion preserves labelled output",
                "For every vertex type V, arbitrary quiver, symbol type alpha, edge labelling, "
                + "strongly connected component S and actual internal path H, the output of "
                + "its ambient image under the original labels is exactly its internal output "
                + "under componentLabel label S. No finiteness assumption is needed."),
            Def("Cyclic", "Cyclicity uses an actual positive return",
                "Cyclic S means that there are q in Component S and an actual "
                + "internal return C : Quiver.Path q q with positive path length. "
                + "A one-vertex component is cyclic exactly when a positive return exists."),
            Def("SynchronizedAt", "Exact LCM synchronization",
                "SynchronizedAt label q requires, for every pair of actual positive "
                + "q-return paths A and B, equality of wordPower(L/length A)(output A) "
                + "and wordPower(L/length B)(output B), where L is the least common "
                + "multiple of their path lengths. It does not assume unique returns "
                + "or unique graph paths."),
            Def("Coherent", "Synchronization at some component basepoint",
                "Coherent label S asserts that SynchronizedAt holds at some actual "
                + "vertex of Component S under the restricted edge labels."),
            Def("BoundedPhases", "Positive bounded cyclic block and all-edge laws",
                "BoundedPhases label S asserts existence of a natural p with "
                + "1 <= p <= Nat.card(Component S), a cyclic word P : ZMod p -> alpha "
                + "and a phase theta : Component S -> ZMod p. Every actual internal "
                + "arrow e : a -> b has label P(theta a) and theta b = theta a + 1. "
                + "A function on the p residues is a word with exactly p positions."),
            Def("PeriodicPrefixes", "One purely periodic stream per entry",
                "For every entry a in Component S there exist one stream X : Nat -> alpha "
                + "and one positive period p, with X(n+p)=X(n) for every n. For every "
                + "actual finite internal path H from a and every i < length H, "
                + "output(H)[i]? = some(X(i)). Empty paths are included."),
            Def("returnPower", "Powers of actual returns",
                "returnPower A 0 is the empty return. returnPower A (k+1) is A "
                + "composed with returnPower A k, retaining every arrow of every copy."),
            Def("PowerTemplate", "Power and literal segments",
                "A PowerTemplate is a finite list of pairs (P,a) of finite words. "
                + "Each pair contributes P to a chosen nonnegative power followed by "
                + "literal a. An empty P is only a literal segment. Omitting empty "
                + "blocks and concatenating neighboring literals gives the conventional "
                + "form a0 P1^k1 a1 ... Pd^kd ad, with every counted Pi nonempty."),
            Def("templateOutput", "Evaluate a fixed template",
                "templateOutput t k concatenates wordPower(k(0))(P), the first literal "
                + "and the remaining template evaluated with i mapped to k(i+1). "
                + "The blocks and literals are fixed before the exponents are chosen."),
            Def("factorCount", "Count only positive periodic blocks",
                "factorCount t is the number of segments whose power block is nonempty. "
                + "Literal-only segments and the empty template contribute zero factors."),
            Def("visitedComponents", "Actual visited component set",
                "visitedComponents H is the finite set of native SCC classes of the "
                + "vertices in H, including both endpoints. The SCC-run construction "
                + "proves that after leaving a component the path cannot revisit it."),
            Def("visitedCyclicCount", "Path-specific cyclic component count",
                "visitedCyclicCount H counts the cyclic components in visitedComponents H. "
                + "Since the component runs cannot revisit a class, it is the number "
                + "of cyclic SCCs in this path's compressed component itinerary."),
            Def("FiniteTemplateCover", "One finite family covers every actual path",
                "There is one finite set T of PowerTemplate values such that for every "
                + "actual finite graph path H, some t in T and some nonnegative exponent "
                + "tuple k satisfy output H = templateOutput t k and "
                + "factorCount t <= visitedCyclicCount H. Zero-factor templates, empty "
                + "paths, acyclic graphs and paths through several cyclic SCCs are allowed."),
            Def("TwoLoopVertex", "Two distinct example vertices",
                "TwoLoopVertex has constructors left and right. The type has exactly "
                + "these two vertices and carries the displayed finite instance."),
            Def("TwoLoopArrow", "Actual example arrows",
                "TwoLoopArrow has a left loop, a right loop and one directed "
                + "bridge from left to right. These are the only arrows of the "
                + "example quiver; there is no reverse bridge."),
            Def("twoLoopLabel", "Two loops and a directed bridge",
                "The example graph has vertices left and right, a loop at each vertex "
                + "and one arrow from left to right. Over Fin 3 the left loop has "
                + "symbol 0, the right loop symbol 1 and the bridge symbol 2. "
                + "Its two cyclic SCCs are distinct and coherent."),
            Def("twoLoopCrossing", "Actual crossing paths with two exponents",
                "twoLoopCrossing i j traverses the left loop i times, then the bridge, "
                + "then the right loop j times. It is an actual left-to-right path; "
                + "the graph also contains noncrossing paths."),
            Def("twoLoopWord", "The crossing sublanguage",
                "twoLoopWord i j is 0^i 2 1^j. For every n, the words indexed by "
                + "i in Fin(n+1) with j=n-i are distinct and have length n+1."),
            Def("SinglePowerTemplate", "Single-power templates include literal exceptions",
                "SinglePowerTemplate stores fixed words before, block and after. "
                + "An empty block permits a fixed literal exception, so the obstruction "
                + "also excludes finite single-power families enlarged by finite literals."),
            Def("singlePowerOutput", "Evaluate a single-power template",
                "singlePowerOutput t k is t.before followed by wordPower k t.block "
                + "and then t.after, for any nonnegative k."),
            Def("TwoLoopBoundary", "Growing output counts and no finite single-power cover",
                "The two native SCCs are distinct and cyclic, every cyclic component "
                + "is coherent, all crossing paths have the displayed outputs, and "
                + "there are n+1 distinct crossing outputs of length n+1 for every n. "
                + "No fixed finite set of SinglePowerTemplate values covers all of "
                + "these outputs. This is an output-language obstruction; no observer "
                + "history or decoder-width model is introduced."),
            Proof("coherent_component_phases", "The complete local equivalence",
                "For every finite vertex type, arbitrary arrow-valued quiver, symbol "
                + "type, edge labels and actual cyclic SCC S, Coherent label S is "
                + "equivalent to BoundedPhases label S, and BoundedPhases label S is "
                + "equivalent to PeriodicPrefixes label S. Coherence also implies "
                + "SynchronizedAt at every component vertex. A positive actual return "
                + "defines a repeated stream. LCM synchronization identifies every "
                + "positive return stream; minimal-period facts give positivity "
                + "and divisibility. Common closing paths give residue independence, "
                + "completed edges give both edge laws, and the first p positions "
                + "of the chosen return give surjectivity onto the p residues, hence "
                + "p is at most the number of component vertices. No phase, primitive "
                + "root, return divisibility, determinism or short-cycle bound is assumed."),
            Proof("result", "Local characterization, finite global cover and two-loop obstruction",
                "For every finite labelled quiver with finite output alphabet, the "
                + "local characterization holds for every cyclic SCC. If every cyclic "
                + "SCC is coherent, FiniteTemplateCover holds. The same conclusion "
                + "includes TwoLoopBoundary. The global construction cuts actual paths "
                + "into SCC runs, proves no revisit using native mutual reachability, "
                + "writes each cyclic run as a rotated block power and bounded remainder, "
                + "and enumerates one finite family of bounded output signatures. "
                + "The factor bound uses the cyclic components visited by that particular "
                + "path. In the two-loop graph each single-power template contributes "
                + "at most one output of any fixed length; the n+1 distinct crossing "
                + "outputs therefore exclude a finite single-power cover. The multipower "
                + "form permits growing fixed-length output counts and supplies no "
                + "uniform candidate-width conclusion by itself. No conclusion about "
                + "a particular observation history or decoder is asserted."))));

    private static DocumentBlock Def(string name, string title, string prose) =>
        Node(name, title, prose, DescribeRole.Definition);

    private static DocumentBlock Proof(string name, string title, string prose) =>
        Node(name, title, prose, DescribeRole.Theorem);

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
