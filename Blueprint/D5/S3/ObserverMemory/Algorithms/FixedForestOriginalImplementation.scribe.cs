using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class FixedForestOriginalImplementationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A feasible original assignment yields a total stationary table faithful to every finite physical history.",
        H("Stationary realization of a fixed physical forest"),
        Blocks(
            Paragraph(Text(
                "For arbitrary P>1, h, ell and e, fix the entire original physical forest and prescribed "
                + "source identifications, assume structural compatibility and choose any "
                + "injective same-digit assignment hitting every extra target. The nominal carrier is the "
                + "disjoint sum Terminal(ZMod(3P)), Read(Unit+Target), Prefix(Fin ell) and "
                + "Tail(Sigma q, Fin(L(q))). The stationary instruction table sees only this control tag. "
                + "Wait adds one, read preserves phase and returns the absolute physical digit, and "
                + "each terminal stores its original x. No time, phase, input label or history is a table input.")),
            Paragraph(Text(
                "Each occupied row requests the source node's literal wait and target, or its original leaf label. "
                + "H/K and H1/K1 each have a common request. Tail index j means j+1 remaining unit waits; "
                + "prefix states perform exactly ell unit waits. Unoccupied digits use the existing H_0. "
                + "All nominal tags are charged, even before reachability is established. "
                + "Neither read-control acyclicity nor any bound of waits by P is imposed.")),
            Paragraph(Text(
                "OriginalImplementation presents the fixed raw domain on any finite nominal controller. "
                + "Its fields preserve the entire original word and all-input event configurations, literal "
                + "continuations, precisely the A/B binary target merge, the common production and resolving "
                + "targets, resolving separation, distinct prescribed shared rows, J=Xi=1 and the exact actual "
                + "read count. History and target maps are proof metadata, not stationary table inputs. "
                + "The record assumes neither Compatible, an assignment, an injection nor a capacity bound.")),
            Result("incompatible_domain_empty", "incompatible-domain-empty", "The incompatible raw domain is empty",
                Scope(Imp(Call("notCompatible", V("F"), V("R"), V("e")),
                    Call("noOriginalImplementationOnAnyFiniteNominalCarrier", V("F"), V("R"), V("e")))),
                "Forced canonical target equality implies actual read-row equality under the prescribed identities. "
                + "The two prescribed double rows already account for all J+Xi=2 history excess. "
                + "A failed source compatibility check therefore contradicts an original fixed-domain implementation."),
            Result("wordData", "original-word-data", "The constructed original word facts",
                Assigned(Call("OriginalWordData", V("F"),
                    Call("controller", V("F"), V("R"), V("alpha")))),
                "The table proves all prefix waits, exact read events, all positive inter-read waits and the "
                + "fixed final halt for every original label. initialize_original_paths converts these facts "
                + "to Initialized on arbitrary nominal carriers without assuming Initialized or a capacity bound."),
            Result("all_states_reachable", "all-states-reachable", "Every charged tag is reached",
                Assigned(All("state", Call("State", V("F"), V("R"), V("alpha")),
                    Call("Reachable", V("F"), V("R"), V("alpha"), V("state")))),
                "Each core target has a physical arrival and each extra has an ordinary arrival. "
                + "A source request attains every finite joint maximum L and visits its entire tail. "
                + "Every original label reaches its terminal; every original input visits the common prefix. "
                + "This proves control-state reachability, without restricting the codomain."),
            Result("actual_row_correspondence", "actual-row-correspondence", "Actual rows are the placed histories",
                Assigned(Call("actualRowIffHistoryPlacement", V("F"), V("R"), V("alpha"))),
                "An actual initialized read occurs at one original event time; conversely every history has "
                + "a supporting original input. Actual used digit rows are exactly the source placement."),
            Result("operational_realization", "operational-realization", "Original fixed-domain operational construction",
                Assigned(Call("originalOperationalHandoff", V("F"), V("R"), V("alpha"))),
                "For every compatible physical forest and same-digit assignment at arbitrary P>1, h, ell and e, "
                + "the existing controller on the full State carrier has an OriginalImplementation and Initialized witness. "
                + "Every charged state is reachable and its cardinal is 3P+2N+1+ell+2e+sum_q(L(q)-1). "
                + "The readControl map is the tagged read state of each placed history; requestTarget is the tagged "
                + "read state of its next target. Literal Waits follows the existing full unit chain. "
                + "The tagged row injection preserves the exact row and edge images and all edge-fiber cardinalities, "
                + "so canonical J=Xi=1 become rawJ=rawXi=1 on (readControl(n),color(n)). "
                + "Binary target equality is exactly the A/B merge, production and resolving requests agree, "
                + "Z is separate from every binary target and the two shared rows remain distinct. "
                + "The incompatible branch quantifies over this same OriginalImplementation class."),
            Result("nominal_capacity", "nominal-capacity", "Exact charged nominal capacity",
                Scope(All("alpha", Call("Assignment", V("F"), V("R"), V("e")),
                    EqF(Call("card", Call("State", V("F"), V("R"), V("alpha"))),
                        Call("originalCapacity", V("P"), V("ell"), V("e"),
                            Call("jointTailExcess", V("F"), V("R"), V("alpha")))))),
                "The cardinal is 3P+2N+1+ell+2e+sum_q(L(q)-1), with N=3(P-1). "
                + "The exact actual read count is N+1+e, and J=s=Xi=1. Three spare digits at "
                + "one extra target share one joint maximum and are not charged independently."),
            Paragraph(Text(
                "realize retains OriginalImplementation, Initialized, exact events and unit phases, final outputs, all-tag reachability, "
                + "three roots, all 3P original leaves, the actual read inventory, the graph statistics and the capacity formula in one construction. "
                + "The corresponding capacity theorem supplies arbitrary-controller extraction and an attained minimum. The simultaneous "
                + "e=0 threshold formula is a separate statement.")) )));

    private static Formula V(string name) => F.Id(name);
    private static Formula N => Seq(Mathbb, Sp, Grp(V("N")));
    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Sp, Grp(V(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.Add(Comma);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula EqF(Formula a, Formula b) => Seq(a, Eq, b);
    private static Formula All(string n, Formula type, Formula body) =>
        Seq(Forall, Sp, V(n), Colon, type, Comma, Grp(body));
    private static Formula Imp(Formula a, Formula b) => Seq(Grp(a), Implies, Grp(b));
    private static Formula AllN(string[] names, Formula body) =>
        names.Reverse().Aggregate(body, (b, n) => All(n, N, b));
    private static Formula ForestScope(Formula body) => AllN(["P", "h", "ell"],
        All("Node", V("Type"), All("finiteNode", Call("Fintype", V("Node")),
        All("eqNode", Call("DecidableEq", V("Node")), All("hP", Seq(D(1), Lt, V("P")),
        All("F", Call("PhysicalForest", V("P"), V("h"), V("ell"), V("Node"), V("hP")), body))))));
    private static Formula Scope(Formula body) => ForestScope(All("e", N,
        All("R", Call("Prescribed", V("F")), body)));
    private static Formula Assigned(Formula body) => Scope(
        All("alpha", Call("Assignment", V("F"), V("R"), V("e")),
            Imp(Call("Compatible", V("F"), V("R"), V("e")), body)));
    private static DocumentBlock Result(string declaration, string id, string heading,
        Formula statement, string explanation, DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/ObserverMemory/Algorithms/FixedForestOriginalImplementation." + declaration),
            H(heading), StatementSource.FromAuthor(Disp(statement)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(explanation))), role);
}
