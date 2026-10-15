using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeF2EdgeClassificationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeF2EdgeClassification.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One actual F2 Hamilton cycle consists exactly of all native circle edges outside its complete literal cut set and all literal T/E c seams.",
        H("Closed Actual F2 Native Edge Classification"),
        Blocks(
            Paragraph(Text(
                "F2NativeEdge is the union of every complete core native circle and "
                + "every nonzero-gap circle of every remaining contact supplier. "
                + "F2DeletedEdge is the complete literal T cut set together with the "
                + "b cut at every gap of every remaining supplier, including gap "
                + "zero, whose cut opens the actual contact circle. F2Seam consists "
                + "of every actual T seam and every actual E seam. All three "
                + "predicates are specified before a walk is selected.")),
            Describe.Lean(DescribeId.Create("native-f2-hamiltonian-cycle-with-closed-inventory"),
                DeclarationHandle.Create(Prefix + "native_f2_hamiltonian_cycle_with_closed_inventory"),
                H("The Same Hamilton Witness Has Exactly the Closed Inventory"),
                StatementSource.FromAuthor(InventoryFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every m at least four, one Hamilton cycle w on F2Domain "
                        + "has, for every undirected raw configuration edge e, the "
                        + "exact classification: e occurs in RawEdges(w) if and only "
                        + "if it is a F2NativeEdge outside F2DeletedEdge or a F2Seam. "
                        + "Thus both inclusion and exclusion concern the same actual "
                        + "Hamilton witness, and the recipe contains no chosen walk.")),
                    Paragraph(Text(
                        "The proof first flattens the earned finite contact recursion. "
                        + "The old core keeps exactly the edges outside all contacts "
                        + "opened so far; the added edges are precisely the uncut new "
                        + "circles and seams indexed by those contacts. Each nonzero "
                        + "new gap is disjoint from the entire old core: the core-star "
                        + "intersection is gap zero, and the supplier gap circles are "
                        + "disjoint. Distinct contact stars are disjoint, giving unique "
                        + "owners for all new native circles.")),
                    Paragraph(Text(
                        "Endpoint ownership excludes every other circle's native "
                        + "cut from retained circle edges. Actual coordinate values "
                        + "show c differs from both a and b, so none of the literal "
                        + "seams can reintroduce any native cut. These facts remove "
                        + "the successor exclusions from earlier added edges and "
                        + "identify the complete closed native cut set. Substitution "
                        + "into the existing actual F2 edge certificate proves the "
                        + "displayed iff."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-f2-deleted-edge-disjoint"),
                DeclarationHandle.Create(Prefix + "native_f2_deleted_edge_disjoint"),
                H("Every Literal F2 Native Cut Is Absent"),
                StatementSource.FromAuthor(DisjointFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every F2DeletedEdge is absent from the complete closed inventory. "
                    + "In particular this includes every T cut, every contact b cut "
                    + "and every nonzero-gap b cut. The c-versus-native generator "
                    + "calculation excludes all seams from the native cut set."))), DescribeRole.Theorem),
            Paragraph(Text(
                "The additional six v-marked cuts, their row-by-row positions, the "
                + "five literal J2 words as full components and the all-size recursion "
                + "remain separate obligations. The result here classifies the "
                + "unmarked actual F2 cycle for every m at least four.")))));

    private static Formula InventoryFormula()
    {
        Formula m = F.Id("m"), b = F.Id("base"), w = F.Id("w"), e = F.Id("e");
        Formula domain = Call("F2Domain", m);
        Formula inventory = All("e", Call("Sym2", Call("Configuration", m)),
            new Formula.Logic(Call("Member", e, Call("RawEdges", w)),
                FormulaLogicOperator.Iff, ClosedInventory(m, e)));
        Formula certificate = new Formula.Logic(Call("IsHamiltonianCycle", w),
            FormulaLogicOperator.And, inventory);
        return Disp(All("m", Call("Nat"), Implies(Le(D(4), m),
            Some("base", Call("Vertices", domain),
                Some("w", Call("Walk", Call("domainGraph", domain), b, b), certificate)))));
    }

    private static Formula DisjointFormula()
    {
        Formula m = F.Id("m"), e = F.Id("e");
        return Disp(All("m", Call("Nat"), Implies(Le(D(4), m),
            All("e", Call("Sym2", Call("Configuration", m)),
                Implies(Call("F2DeletedEdge", m, e), Neg(ClosedInventory(m, e)))))));
    }

    private static Formula ClosedInventory(Formula m, Formula e) =>
        new Formula.Logic(new Formula.Logic(Call("F2NativeEdge", m, e),
            FormulaLogicOperator.And, Neg(Call("F2DeletedEdge", m, e))),
            FormulaLogicOperator.Or, Call("F2Seam", m, e));
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
    private static Formula Neg(Formula a) => new Formula.Not(a);
}
