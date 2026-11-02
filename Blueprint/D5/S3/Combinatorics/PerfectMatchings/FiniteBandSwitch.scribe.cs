using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PerfectMatchings;

internal sealed class FiniteBandSwitchDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PerfectMatchings/FiniteBandSwitch.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RibbonEmbeddings/ghanbarisamal2026facial");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual switch of two band pairs exchanges good and regular and yields equal expectations under an invariant finite law.",
        H("Band Switching and Expectation Symmetry"),
        Blocks(
            Paragraph(Text("Let X be a finite flag carrier. The permutations s and t are involutions "
                + "without fixed points, representing corner and band matchings. For four distinct points "
                + "a,b,t(a),t(b), let u swap t(a) and t(b), and let t'=u*t*u. "
                + "This replaces a--t(a), b--t(b) by a--t(b), b--t(a) and leaves all other pairs unchanged. "
                + "Good(s,t,a,b) means that a and b are in the same integer-power orbit of s*t. "
                + "Bad(s,t,a,b) means that s(a) and b are in the same such orbit. "
                + "Regular(s,t,a,b) means that neither orbit relation holds. "
                + "The two-matching connectivity theorem identifies Regular with distinct combinatorial boundary components.")),
            Describe.Lean(DescribeId.Create("band-switch"), DeclarationHandle.Create(Prefix + "band_switch"),
                H("Actual Band Surgery Exchanges the Categories"), StatementSource.FromAuthor(SwitchFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Delete the two selected band pairs by fixing their four endpoints. "
                    + "First-return paths in the remaining finite matching system construct a fixed-point-free endpoint pairing. "
                    + "Its value at one endpoint and involutivity force one of the three pairings of four points. "
                    + "The proved reattachment orbit formula then gives good-to-regular, regular-to-good, and bad-to-bad. "
                    + "The cut and both reattachments are explicitly identified with t and u*t*u; their orbit effect is not a premise."))),
                DescribeRole.Theorem),
            Paragraph(Text("For the expectation statement, Omega is a nonempty finite set of equally weighted states. "
                + "The corner matching s is fixed and t(omega) is a fixed-point-free involutive band matching for every state. "
                + "The four marked points are distinct in every state. A state bijection tau satisfies "
                + "t(tau(omega)) = switch(t(omega),a,b) for each omega, where switch is the actual matching operation above. "
                + "MeanGood and MeanPhysicalRegular are the rational sums of the corresponding zero-one indicators "
                + "divided by card(Omega). PhysicalRegular is the negation of corner/band connectivity.")),
            Describe.Lean(DescribeId.Create("twist-expectation"),
                DeclarationHandle.Create(Prefix + "twist_invariant_uniform_expectation"),
                H("Equal Good and Regular Expectations Under the Stated Law"),
                StatementSource.FromAuthor(ExpectationFormula()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Band surgery proves that a state's regular indicator equals the good indicator "
                    + "of its image under tau. Reindexing the finite sum gives equality of the two means. "
                    + "The statement makes the state-space and actual matching-transport assumptions explicit. "
                    + "It does not identify an unspecified distribution on unlabelled embeddings, prove surface realization, "
                    + "or imply exact thirds for any category."))), DescribeRole.Theorem),
            new DocumentBlock.Section(
                H("Application to Independent Signed Rotations"),
                Blocks(
            Paragraph(Text("Let G be a finite simple cubic graph, with vertex set V, edge set E, "
                + "and dart set D consisting of ordered adjacent vertex pairs. At each vertex choose a "
                + "labelling of its three neighbours. The forward and inverse 3-cycles are its two cyclic "
                + "orders; among the six shuffled neighbour lists, each cyclic order has three representatives. "
                + "Thus independent uniform cyclic orders and independent fair edge signs have the uniform "
                + "state space Omega = Bool^V times Bool^E, of size 2^(card(V)+card(E)). "
                + "This is the full labelled signed-rotation law, with every rotation and sign retained.")),
            Paragraph(Text("For a sampled rotation rho, write R(d) for the dart obtained by rotating "
                + "the neighbour at the initial vertex of d. On X = D times Bool define "
                + "P(d,1) = (R(d),0), P(d,0) = (R^(-1)(d),1), and "
                + "L(d,b) = (reverse(d), b xor lambda(edge(d))). "
                + "Here lambda is the sign bit in the neighbour-list sampler: zero preserves side across "
                + "a band and one reverses it. P and L are involutions. P has no fixed points because "
                + "it reverses side; L has none because the adjacent vertices of a simple graph are distinct. "
                + "The P/L components are the physical facial boundaries, and each has the two disjoint "
                + "oriented P*L orbits given by the matching-component decomposition.")),
            Paragraph(Text("Fix an edge and choose either of its darts d. Put a=(d,0) and b=(d,1). "
                + "The four flags a,b,L(a),L(b) are distinct, independently of its sign. "
                + "GoodAt(P,L,a,b) says the two edge sides occur in one oriented boundary orbit, "
                + "so their directed traversals agree. BadAt uses the opposite oriented orbit, represented "
                + "by P(a), so the traversals oppose. PhysicalRegularAt says the sides lie in different "
                + "P/L components. The disjoint two-orbit decomposition makes these three categories "
                + "mutually exclusive and exhaustive, including singleton product orbits.")),
            Paragraph(Text("Toggle only the chosen edge sign. On the same flag carrier and with the "
                + "same corner matching this changes L to u*L*u, where u swaps L(a) and L(b). "
                + "Every other band pair is unchanged. The actual cut and its two reattachments therefore "
                + "satisfy band_switch, which exchanges good and regular and preserves bad. In particular "
                + "the third endpoint pairing is bad under both signs; components missing the four flags "
                + "remain present. For each fixed rotation, apply twist_invariant_uniform_expectation "
                + "to the whole sign-vector space and its one-coordinate toggle. Summing this equality "
                + "over all rotation vectors gives equal good and regular probabilities for every edge "
                + "under the full uniform law.")),
            Paragraph(Text("Let G_count, B_count and R_count count edges in the three physical categories. "
                + "For each state their sum is card(E). Interchanging the finite state and edge sums "
                + "in the per-edge equality gives E[G_count]=E[R_count]. Averaging the partition identity "
                + "then gives E[G_count]=E[R_count]=(card(E)-E[B_count])/2. "
                + "These finite averages are exactly the expectations under the stated uniform law. "
                + "There is no connectedness, bridgelessness, orientability or edge-transitivity premise. "
                + "The empty graph has vacuous edge assertions and all three counts zero. "
                + "The conclusion imposes no exact-thirds identity.")))))));

    private static Formula V(string x) => F.Id(x);
    private static Formula All(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), domain, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Matching(Formula p) => And(Call("Involutive", p), Call("FixedPointFree", p));
    private static Formula Type(string name, Formula t) => Call(name, V("s"), t, V("a"), V("b"));
    private static Formula Switched() => Call("switch", V("t"), V("a"), V("b"));
    private static Formula SwitchFormula() => Disp(All("X", V("FiniteType"),
        All("s", Call("Perm", V("X")), All("t", Call("Perm", V("X")),
        All("a", V("X"), All("b", V("X"),
            Imp(And(And(Matching(V("s")), Matching(V("t"))),
                Call("FourDistinct", V("a"), V("b"), Call("apply", V("t"), V("a")), Call("apply", V("t"), V("b")))),
                And(Iff(Type("Good", Switched()), Type("Regular", V("t"))),
                    And(Iff(Type("Bad", Switched()), Type("Bad", V("t"))),
                        Iff(Type("Regular", Switched()), Type("Good", V("t"))))))))))));
    private static Formula ExpectationFormula() => Disp(All("X", V("FiniteType"),
        All("Omega", V("NonemptyFiniteType"), All("s", Call("Perm", V("X")),
        All("t", Call("Function", V("Omega"), Call("Perm", V("X"))),
        All("tau", Call("Equiv", V("Omega"), V("Omega")),
        All("a", V("X"), All("b", V("X"),
            Imp(Call("ActualTwistFamily", V("s"), V("t"), V("tau"), V("a"), V("b")),
                Equal(Call("MeanGood", V("s"), V("t"), V("a"), V("b")),
                    Call("MeanPhysicalRegular", V("s"), V("t"), V("a"), V("b"))))))))))));
}
