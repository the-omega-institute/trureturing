using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;
internal sealed class FiniteInstrumentRelationGraphDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Static relation semantics of genuine finite adaptive quantum instrument protocols.",
        H("Finite instruments as a fixed quantum relation graph"),
        Blocks(Describe.Lean(DescribeId.Create("relation-graph-protocol-correspondence"),
            DeclarationHandle.Create("D5/S3/Quantum/Dynamics/FiniteInstrumentRelationGraph.relation_graph_protocol_correspondence"),
            H("Unique local relation solution preserves every actual record"),
            StatementSource.FromAuthor(Disp(All("A",Call("Type"),Instance(Call("Fintype",F.Id("A")),Instance(Call("DecidableEq",F.Id("A")),All("R",Call("Type"),Instance(Call("Fintype",F.Id("R")),All("F",Call("Type"),All("d",Call("Function",F.Id("A"),Call("Nat")),All("T",Call("FiniteLocalProtocolTree",F.Id("F"),F.Id("d")),All("X",Call("State",F.Id("R"),F.Id("d")),Unique("phi",Call("Assignment",F.Id("R"),F.Id("T")),Conj(Call("GraphLaw",F.Id("phi")),Rel(Call("rootValue",F.Id("phi")),Eq,F.Id("X")),Rel(Call("graphLeaves",F.Id("phi")),Eq,Call("terminalOutputs",F.Id("T"),F.Id("X"))),Rel(Call("graphPrefixes",F.Id("phi")),Eq,Call("coarsePrefixes",F.Id("T"),F.Id("X"))),Rel(Call("SumTerminalTrace",Call("graphLeaves",F.Id("phi"))),Eq,Call("Trace",F.Id("X")))))))))))))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumChannels/chiribella2009networks")),
            Blocks(
                Paragraph(Text("The protocol data are the canonical FiniteLocalProtocol.Tree: a finite inductive tree of completely positive instruments, finite actual outcomes, outcome-dependent interface dimensions, and a feedback value at each terminal. Each instrument is trace preserving after summing actual outcomes. Hidden Kraus labels do not control the child function. This covers arbitrary finite feedback and early termination. The input reference factor is untouched; any environment which interacts again is held in the active interface, not traced out as inaccessible garbage.")),
                Paragraph(Text("Unroll the finite actual-outcome branches into a fixed rooted graph. Put an independent full matrix variable at each prefix vertex. The graph law is only the neighboring equation X(ha)=J(a|h)(X(h)), with the canonical spectator extension on the full correlated interface. These are actual CP constraints; a global protocol equality is not a graph hypothesis. Recursion constructs one solution from the input boundary. Induction forces any other local solution to equal it at every vertex. Independently reading assigned prefix and terminal vertices gives exactly canonical coarsePrefixes and terminalOutputs, including each actual record, feedback value, interface and matrix. Canonical complete_subtree_trace gives terminal total trace on every input matrix.")),
                Paragraph(Text("The same construction works for a protocol with independent ancillary densities by applying it to appendAncillas of its input. FiniteLocalProtocol.recursive_coarse_retained preserves both all prefixes and terminals while keeping inaccessible Kraus outputs through the complete execution and tracing them only for the reported coarse output. Returning environments belong to the active system and therefore remain available to later operations. For positive trace-one input the canonical instrument semantics give nonnegative joint probabilities and total one. Born probabilities and complete positivity remain explicit quantum representation assumptions."))),
            DescribeRole.Theorem))));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Open, Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body, Close);
    private static Formula Unique(string name, Formula type, Formula body) =>
        Seq(Open, Exists, Sp, Bang, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body, Close);
    private static Formula Rel(Formula left, Formula relation, Formula right) =>
        Seq(Open, left, Sp, relation, Sp, right, Close);
    private static Formula Conj(params Formula[] statements) =>
        statements.Aggregate((left, right) => Rel(left, Land, right));
    private static Formula Instance(Formula instance, Formula body) =>
        Seq(OpenBracket, instance, CloseBracket, Sp, body);
}
