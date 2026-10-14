using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeJ2MarkedPortsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2MarkedPorts.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The twelve independently defined native J2 ports are distinct, and the six actual marked b cuts have disjoint endpoints.",
        H("Actual Native J2 Marked Ports"),
        Blocks(
            Paragraph(Text(
                "A port is indexed by i in Fin(3), a Boolean exchanging the actual values p=0 and q=m, "
                + "and a Boolean choosing the left side. Right ports are the independently defined "
                + "R0=(q,p,A,v), R1=(p,A,q,v), R2=(A,q,p,v), with A=(1,...,m-2) and v=m-1. "
                + "Left ports multiply the corresponding right port by the actual length-m reversal b. "
                + "The label exchange acts by left multiplication, so it commutes with every reversal of positions.")),
            Node("native-j2-port-injective", "native_j2_port_injective", "Twelve Distinct Actual Vertices",
                Scoped(Call("Injective", Call("port", F.Id("m")))),
                "For every m at least five, port(m) is injective on Fin(3) times Bool times Bool. "
                + "The proof compares actual permutation values at positions 0, 1, 2 and m-1. "
                + "These coordinates distinguish every possible pair, including the opposite orientations of A."),
            Node("native-j2-port-last", "native_j2_port_last", "The Common Actual Terminal Label",
                Scoped(All("p", PortIndex(), Eq(Call("val", Call("apply", Call("port", F.Id("m"), F.Id("p")),
                    Call("last", F.Id("m")))), Call("sub", F.Id("m"), D(1))))),
                "For every m at least five, every port has actual terminal value m-1. "
                + "This follows from the native reversal, rotation and label-swap formulas, rather than an assumed tuple interpretation."),
            Node("native-j2-marked-edge", "native_j2_marked_edge", "Actual Generator Edges",
                Disp(All("m", Call("Nat"), All("p", CutIndex(), Eq(Call("markedEdge", F.Id("m"), F.Id("p")),
                    Call("symPair", RightEndpoint(), Call("mul", RightEndpoint(), Call("b", F.Id("m")))))))),
                "Each marked pair is exactly the undirected b-generator edge from its right port. "
                + "This identity holds at every size; the left/right correspondence is part of the actual permutation definitions."),
            Node("native-j2-marked-disjoint", "native_j2_marked_disjoint", "Disjoint Endpoints of the Six Cuts",
                Scoped(All("p", CutIndex(), All("q", CutIndex(), Implies(
                    Ne(F.Id("p"), F.Id("q")), Call("Disjoint", Call("endpoints", Call("markedEdge", F.Id("m"), F.Id("p"))),
                        Call("endpoints", Call("markedEdge", F.Id("m"), F.Id("q")))))))),
                "For every m at least five, two different indices in Fin(3) times Bool give cuts with no endpoint in common. "
                + "A shared actual endpoint would contradict the proved twelve-port injection."),
            Paragraph(Text(
                "These results prove the actual marked-cut geometry. Membership of the cuts in one particular F2 Hamilton witness, "
                + "legality of the five literal J2 words, exhaustion of path components and all-size Hamiltonicity require separate proofs.")))));

    private static DocumentBlock Node(string id, string selector, string title, Formula statement, string proof) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + selector), H(title),
            StatementSource.FromAuthor(statement), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(proof))), DescribeRole.Theorem);

    private static Formula RightEndpoint() => Call("port", F.Id("m"),
        Call("tuple", Call("fst", F.Id("p")), Call("snd", F.Id("p")), Call("false")));
    private static Formula CutIndex() => Call("Prod", Call("Fin", D(3)), Call("Bool"));
    private static Formula PortIndex() => Call("Prod", Call("Fin", D(3)), Call("Prod", Call("Bool"), Call("Bool")));
    private static Formula Scoped(Formula body) => Disp(All("m", Call("Nat"), Implies(Le(D(5), F.Id("m")), body)));
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
            : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.Equal, r);
    private static Formula Ne(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.NotEqual, r);
    private static Formula Le(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.LessThanOrEqual, r);
    private static Formula Implies(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.Implies, r);
}
