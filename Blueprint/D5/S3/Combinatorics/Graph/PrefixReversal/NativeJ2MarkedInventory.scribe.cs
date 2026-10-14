using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeJ2MarkedInventoryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2MarkedInventory.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All twelve independently defined J2 ports are actual F2 vertices, and one actual F2 Hamilton witness contains all six marked b edges while retaining its exact full edge inventory.",
        H("Actual J2 Marked Edges in One F2 Hamilton Witness"),
        Blocks(
            Describe.Lean(DescribeId.Create("native-j2-right-owner"),
                DeclarationHandle.Create(Prefix + "rightOwner"),
                H("The Six Actual Native Circle Owners"),
                StatementSource.FromAuthor(RightOwnerFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let j=m-3 and let tau exchange labels zero and m. The six independently "
                    + "specified right-port owners are identity, tau, contactAnchor(j), lowerPort(j), "
                    + "gapAnchor(contactAnchor(j),m-1), and gapAnchor(contactAnchor(j),m-2), "
                    + "indexed by the three port numbers and their label-swap bits. The actual "
                    + "surviving circle rows consume these exact owners."))), DescribeRole.Definition),
            Node("native-j2-port-circle", "native_j2_port_circle", "Every Actual Port Has Its Specified Native Owner",
                Scoped(All("p", PortIndex(), Call("Circle",
                    Call("rightOwner", F.Id("m"), Call("CutIndexOf", F.Id("p"))),
                    Call("port", F.Id("m"), F.Id("p"))))),
                "For every m at least five, each actual port lies in the native circle anchored by "
                + "rightOwner at the same right-port number and label-swap bit. The six right-port "
                + "rotation identities establish this for the right endpoints. Multiplication by b "
                + "stays in the same independently specified native circle, giving the left endpoints. "
                + "Port-domain membership and exclusion of marked edges from intermediate complete "
                + "native-circle complements consume this owner fact."),
            Node("native-j2-port-domain", "native_j2_port_domain", "Every Actual J2 Port Belongs to F2",
                PortDomainFormula(),
                "For every m at least five and p in Fin(3) times Bool times Bool, port(m,p) lies in the "
                + "independently specified F2Domain. Let j=m-3, rho=finRotate(m+1), and T exchange the "
                + "actual labels 0 and m. The six right ports have the precise native-owner identities "
                + "R0=rho^m, bar(R0)=T*rho^m, R1=contactAnchor(j)*rho^m, "
                + "bar(R1)=lowerPort(j)*rho, R2=gapAnchor(contactAnchor(j),m-1)*rho, and "
                + "bar(R2)=gapAnchor(contactAnchor(j),m-2)*rho^2. The first two belong to the two normalized "
                + "core-cut circles, the fourth to a lower T circle, and the remaining ones to actual "
                + "contact-supplier gap circles. Actual rotations preserve each full native circle. Each "
                + "left port is the corresponding right port multiplied by b, so the earned native-edge "
                + "endpoint law places it in the same owner circle. The proof uses the earned complete "
                + "core and supplier partitions, rather than assuming port membership."),
            Node("native-j2-marked-uncut", "native_j2_marked_uncut", "All Six Actual Marked Edges Avoid the Full T/E Cut Set",
                MarkedUncutFormula(),
                "For every m at least five and p in Fin(3) times Bool, markedEdge(m,p) does not belong "
                + "to F2DeletedEdge. The marked-edge identity makes it the actual b edge at its right "
                + "port. Every actual port has terminal value m-1, while the complete b-cut "
                + "classification permits only terminal 0 in a lower T circle or contact supplier and "
                + "terminal m in an upper T circle. Since m-1 differs from both, every marked edge is uncut. "
                + "This is a consumed application of the existing terminal and complete cut classification."),
            Node("native-j2-hamiltonian-cycle-with-marked-edges", "native_j2_hamiltonian_cycle_with_marked_edges",
                "One and the Same Hamilton Cycle Contains Every Marked Edge", InventoryFormula(),
                "For every m at least five, there is one actual Hamilton cycle w on F2Domain with all "
                + "three facts simultaneously: its raw undirected edges have the exact full closed "
                + "F2 inventory; all twelve actual J2 ports lie in its vertex domain; and all six "
                + "marked edges occur in its raw edge list. The witness is obtained once from the "
                + "earned native-edge inventory theorem. Its actual native-edge retention criterion "
                + "then applies to each marked right port using the proved domain membership and "
                + "the proved exclusion from the full cut set. The closed inventory is retained "
                + "unchanged for that same witness: an arbitrary raw edge occurs exactly when it is "
                + "a native F2 edge outside F2DeletedEdge or an actual F2Seam."),
            Paragraph(Text(
                "The independently proved twelve-port injection gives the six marked cuts disjoint endpoints. "
                + "This layer places those cuts in one specific certified F2 Hamilton witness. "
                + "Legality of the five literal J2 words after the six cuts, their nonbacktracking paths, "
                + "exhaustion of path components, and all-size Hamiltonicity remain separate obligations.")))));

    private static DocumentBlock Node(string id, string selector, string title, Formula statement, string proof) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + selector), H(title),
            StatementSource.FromAuthor(statement), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(proof))), DescribeRole.Theorem);

    private static Formula RightOwnerFormula()
    {
        Formula m = F.Id("m"), j = Call("sub", m, D(3));
        Formula c = Call("contactAnchor", j);
        Formula Owner(byte i, bool swapped) => Call("rightOwner", m,
            Call("Pair", D(i), Call(swapped ? "BoolTrue" : "BoolFalse")));
        Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
        return Scoped(And(Eq(Owner(0, false), D(1)),
            And(Eq(Owner(0, true), Call("Swap", D(0), m)),
            And(Eq(Owner(1, false), c), And(Eq(Owner(1, true), Call("lowerPort", j)),
            And(Eq(Owner(2, false), Call("gapAnchor", c, Call("sub", m, D(1)))),
                Eq(Owner(2, true), Call("gapAnchor", c, Call("sub", m, D(2))))))))));
    }

    private static Formula PortDomainFormula()
    {
        Formula m = F.Id("m"), p = F.Id("p");
        return Scoped(All("p", PortIndex(), Call("F2Domain", m, Call("port", m, p))));
    }

    private static Formula MarkedUncutFormula()
    {
        Formula m = F.Id("m"), p = F.Id("p");
        return Scoped(All("p", CutIndex(), Neg(Call("F2DeletedEdge", m, Call("markedEdge", m, p)))));
    }

    private static Formula InventoryFormula()
    {
        Formula m = F.Id("m"), b = F.Id("base"), w = F.Id("w"), e = F.Id("e"), p = F.Id("p");
        Formula domain = Call("F2Domain", m);
        Formula rawInventory = All("e", Call("Sym2", Call("Configuration", m)),
            new Formula.Logic(Call("Member", e, Call("RawEdges", w)), FormulaLogicOperator.Iff,
                Or(And(Call("F2NativeEdge", m, e), Neg(Call("F2DeletedEdge", m, e))),
                    Call("F2Seam", m, e))));
        Formula ports = All("p", PortIndex(), Call("F2Domain", m, Call("port", m, p)));
        Formula marked = All("p", CutIndex(), Call("Member", Call("markedEdge", m, p), Call("RawEdges", w)));
        return Scoped(Some("base", Call("Vertices", domain),
            Some("w", Call("Walk", Call("domainGraph", domain), b, b),
                And(Call("IsHamiltonianCycle", w), And(rawInventory, And(ports, marked))))));
    }

    private static Formula CutIndex() => Call("Prod", Call("Fin", D(3)), Call("Bool"));
    private static Formula PortIndex() => Call("Prod", Call("Fin", D(3)), Call("Prod", Call("Bool"), Call("Bool")));
    private static Formula Scoped(Formula body) =>
        Disp(All("m", Call("Nat"), Implies(Le(D(5), F.Id("m")), body)));
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
            : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Some(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Neg(Formula a) => new Formula.Not(a);
}
