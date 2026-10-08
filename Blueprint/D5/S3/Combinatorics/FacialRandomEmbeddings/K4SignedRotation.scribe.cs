using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FacialRandomEmbeddings;

internal sealed class K4SignedRotationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FacialRandomEmbeddings/K4SignedRotation.";

    private const string CorePrefix = Prefix;

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For the uniform signed-rotation law on K4, none of the three boundary types has expected count two.",
        H("K4 Signed Ribbons and the Dyadic Obstruction"),
        Blocks(
            Paragraph(Text(
                "Let Omega be a finite set of equally weighted states, E an event-index set, and T a decidable relation. "
                + "EventCount(T,e) counts the states omega satisfying T(omega,e). TotalCount(T) counts all incident "
                + "pairs (omega,e), with the state index summed first. UniformExpectedCount(T) is "
                + "TotalCount(T) divided by the cardinality of Omega, in the rational numbers. "
                + "EventTransport(T,phi,e,f) means that T(phi(omega),f) is equivalent to T(omega,e) for every omega. "
                + "Transport(T,root) means that for every e in E there is a bijection phi of Omega such that "
                + "T(phi(omega),e) if and only if T(omega,root), for every omega. "
                + "These are actual event-preserving bijections; equality of marginal probabilities is a conclusion.")),
            Describe.Lean(DescribeId.Create("transport-marginal-count"),
                DeclarationHandle.Create(CorePrefix + "event_count_eq_of_equiv"),
                H("A State Bijection Preserves Event Cardinality"),
                StatementSource.FromAuthor(MarginalFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Reindex the finite sum along phi. Its pointwise event equivalence identifies every summand, "
                    + "so the two event counts are equal. The event-index type need not be finite for this step."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("transitive-double-count"),
                DeclarationHandle.Create(CorePrefix + "total_count_eq_card_mul"),
                H("Double Counting a Transitive Event Family"),
                StatementSource.FromAuthor(TotalFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Interchange the two finite sums. Every event column has the root event's cardinality, "
                    + "so the total number of incidences is the number of event indices times the root cardinality."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("expectation-denominator"),
                DeclarationHandle.Create(CorePrefix + "expected_denominator_dvd"),
                H("The State Count Must Absorb the Denominator"),
                StatementSource.FromAuthor(DenominatorFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For nonempty Omega and a chosen root in E, equating the uniform mean with card(E)/q "
                    + "and clearing the nonzero denominators gives q times the root count equal to card(Omega). "
                    + "Thus q divides the state-space cardinality. No primality or coprimality assumption is needed."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("dyadic-third-obstruction"),
                DeclarationHandle.Create(CorePrefix + "dyadic_expected_count_ne_third"),
                H("A Dyadic Sample Space Excludes One Third"),
                StatementSource.FromAuthor(DyadicFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If Omega has 2^r elements, a mean of card(E)/3 would force 3 to divide 2^r. "
                    + "Primality of 3 would then force 3 to divide 2, which is impossible. "
                    + "The conclusion concerns the stated uniform finite law; it makes no assertion about "
                    + "nonuniform sampling or a different quotient of the state space."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "For K4 the edge order is 01,02,03,12,13,23. Each edge contributes four flags, "
                + "two sides at its lower endpoint and two at its upper endpoint. Four independently chosen "
                + "rotation bits select ascending or reversed cyclic neighbour orders; six independent twist bits "
                + "select band attachments. Thus State is Fin(16) times Fin(64), containing all 1024 outcomes. "
                + "The corner and band maps are fixed-point-free involutions. "
                + "The face permutation applies band then corner. Its integer-power cycles are oriented "
                + "boundary traversals. The two-matching component theorem proves that each combinatorial boundary "
                + "component consists of two disjoint opposite oriented cycles.")),
            Describe.Lean(DescribeId.Create("physical-classifier"),
                DeclarationHandle.Create(Prefix + "classification_iff"),
                H("The Finite Classifier Has Combinatorial Ribbon Boundary Semantics"),
                StatementSource.FromAuthor(ClassificationFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At a chosen endpoint, good singular means that the two side flags lie in the same "
                    + "oriented face orbit. Bad singular means that they lie in opposite oriented orbits of "
                    + "the same combinatorial boundary component. Regular means that the two side flags lie in different "
                    + "corner/band components. The finite classifier is proved equivalent to these predicates. "
                    + "Permutation orbits on these 24 flags are determined by the first 24 iterates."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exact-third-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("An Exact Third for Some Physical Edge Type"),
                StatementSource.FromAuthor(ClaimFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This closed claim says that at least one of good singular, bad singular or regular "
                    + "has expected count six divided by three under the uniform law on all 1024 states. "
                    + "Negating this existential excludes each equality, which is stronger within this specified "
                    + "law than negating the conjunction of all three equalities."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("k4-uniform-refutation"),
                DeclarationHandle.Create(Prefix + "result"),
                H("All Three Exact-Third Equalities Fail Under the Specified Law"),
                StatementSource.FromAuthor(Disp(new Formula.Not(V("claim")))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Six actual vertex relabellings take edge 01 to every edge. The corresponding state "
                    + "maps are proved bijective. Finite verification of the corner and band intertwinings "
                    + "gives conjugate face permutations, so permutation-orbit transport establishes "
                    + "boundary-classifier equivariance. Applying the finite-event theorem with 1024 = 2^10 excludes mean two "
                    + "for every physical type, without assuming equal marginal probabilities. "
                    + "The law is the independently sampled rotations and signs in the Ghanbari–Šámal public notebook "
                    + "at commit 0d4404941894d3ef8dd9f27f1e61829bec2bcde5. The paper's phrase random embedding "
                    + "does not itself specify a law. This result does not concern uniform unlabelled maps, "
                    + "nonuniform laws, or conditioning on orientability, genus or face count. No resolution "
                    + "of an unspecified-law conjecture, nor any cycle double cover theorem, is asserted. "
                    + "Realization as a closed surface and topological classification are outside this formalization."))),
                DescribeRole.Theorem))));

    private static Formula ClassificationFormula() => Disp(
        All("ty", Call("Fin", D(3)), All("s", V("State"), All("e", V("Edge"),
            new Formula.Logic(Equal(Call("EdgeType", V("s"), V("e")), V("ty")),
                FormulaLogicOperator.Iff, Call("HasType", V("ty"), V("s"), V("e")))))));

    private static Formula ClaimFormula() => Disp(new Formula.Logic(V("claim"),
        FormulaLogicOperator.Iff,
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("ty"), Call("Fin", D(3)),
            Equal(Call("UniformExpectedCount", Call("HasType", V("ty"))), Divide(D(6), D(3))))));

    private static Formula V(string s) => F.Id(s);
    private static Formula Divide(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula All(string s, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), domain, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Card(string s) => Call("card", V(s));
    private static Formula Count(string s) => Call("EventCount", V("T"), V(s));
    private static Formula Mean() => Call("UniformExpectedCount", V("T"));
    private static Formula Transport() => Call("Transport", V("T"), V("root"));
    private static Formula Context(Formula body, bool finiteEvents = true) =>
        Disp(All("Omega", V("FiniteType"), All("E", V(finiteEvents ? "FiniteType" : "Type"),
            All("T", Call("DecidableRelation", V("Omega"), V("E")), body))));
    private static Formula RootContext(Formula body) => Context(All("root", V("E"), Imp(Transport(), body)));

    private static Formula MarginalFormula() => Context(
        All("e", V("E"), All("f", V("E"), All("phi", Call("Equiv", V("Omega"), V("Omega")),
            Imp(Call("EventTransport", V("T"), V("phi"), V("e"), V("f")),
                Equal(Count("e"), Count("f")))))), false);

    private static Formula TotalFormula() => RootContext(
        Equal(Call("TotalCount", V("T")), Multiply(Card("E"), Count("root"))));

    private static Formula DenominatorFormula() => RootContext(
        All("q", V("Nat"), Imp(And(Call("Nonempty", V("Omega")), NotEqual(V("q"), D(0))),
            Imp(Equal(Mean(), Divide(Card("E"), V("q"))), Call("Divides", V("q"), Card("Omega"))))));

    private static Formula DyadicFormula() => RootContext(
        All("r", V("Nat"), Imp(
            Equal(Card("Omega"), new Formula.Power(D(2), V("r"))),
            NotEqual(Mean(), Divide(Card("E"), D(3))))));
}

