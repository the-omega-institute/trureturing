using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeF2EdgeInventoryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeF2EdgeInventory.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One actual Hamilton cycle on the complete F2 supplier union has exactly the arbitrary-edge inventory prescribed by its literal finite contact surgeries.",
        H("Complete Actual F2 Edge Inventory"),
        Blocks(
            Paragraph(Text(
                "PartialEdge(m,0,e) is CoreUncut(m,e) or TSeam(m,e), using the complete "
                + "actual two-star core inventory. At contact k<m-2, PartialEdge keeps "
                + "the preceding edges except the literal edge from contactAnchor(k) "
                + "to contactAnchor(k)b, adds the uncut native circle edges of every "
                + "new gap, and adds the actual E c seams. The recipe is defined "
                + "from the concrete suppliers and their original cuts, before "
                + "choosing any walk.")),
            Describe.Lean(DescribeId.Create("native-f2-hamiltonian-cycle-with-edge-inventory"),
                DeclarationHandle.Create(Prefix + "native_f2_hamiltonian_cycle_with_edge_inventory"),
                H("The Same Complete F2 Cycle Has Exactly the Prescribed Raw Edges"),
                StatementSource.FromAuthor(InventoryFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every m at least four, there is one actual Hamilton cycle w "
                        + "on F2Domain(m) such that, for every undirected edge e of actual "
                        + "configurations, e occurs in the subtype-forgetting image of "
                        + "w.edges exactly when PartialEdge(m,m-2,e) holds. Hamiltonicity "
                        + "and both directions of the edge classification concern the "
                        + "same witness; the inventory does not describe a separately "
                        + "chosen cycle or merely prove selected edges are retained.")),
                    Paragraph(Text(
                        "The finite induction starts from the existing complete core "
                        + "certificate. Its retention law and the concrete exclusion of "
                        + "every future contact edge from CoreDeletedEdge earn the actual "
                        + "pending-edge invariant. Pairwise disjoint complete contact "
                        + "stars ensure that opening the next edge preserves every later "
                        + "contact along this same cycle.")),
                    Paragraph(Text(
                        "At each step the generic actual one-contact graft theorem "
                        + "classifies every raw edge of its Hamilton witness as exactly "
                        + "an old uncut edge, a new uncut native circle edge, or an E seam. "
                        + "Substituting the preceding induction certificate proves the "
                        + "independent PartialEdge successor recipe in both directions. "
                        + "The actual graft domain is PartialDomain(m,k+1); its equality "
                        + "transports Hamiltonicity, pending edges and the whole raw-edge "
                        + "iff together. After m-2 steps the domain is F2Domain(m)."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "This complete recursive edge recipe supports subsequent deletion classification. "
                + "A simplified closed table for the marked J2 paths, the proofs that their "
                + "displayed words are whole components, and all-size recursive Hamiltonicity "
                + "remain separate mathematical obligations.")))));

    private static Formula InventoryFormula()
    {
        Formula m = F.Id("m"), b = F.Id("base"), w = F.Id("w"), e = F.Id("e");
        Formula domain = Call("F2Domain", m);
        Formula inventory = All("e", Call("Sym2", Call("Configuration", m)),
            new Formula.Logic(Call("Member", e, Call("RawEdges", w)), FormulaLogicOperator.Iff,
                Call("PartialEdge", m, Call("NatSub", m, D(2)), e)));
        Formula certificate = new Formula.Logic(Call("IsHamiltonianCycle", w),
            FormulaLogicOperator.And, inventory);
        Formula result = Some("base", Call("Vertices", domain),
            Some("w", Call("Walk", Call("domainGraph", domain), b, b), certificate));
        return Disp(All("m", Call("Nat"), Implies(Le(D(4), m), result)));
    }

    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
            : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Some(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
