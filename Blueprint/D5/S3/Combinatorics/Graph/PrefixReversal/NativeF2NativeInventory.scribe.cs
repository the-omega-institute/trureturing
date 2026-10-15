using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeF2NativeInventoryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeF2NativeInventory.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The independent native-circle catalog is exactly the actual F2 a/b edge set, and one actual Hamilton cycle retains precisely its uncut edges.",
        H("Actual Native F2 Edge Inventory"),
        Blocks(
            Describe.Lean(DescribeId.Create("native-f2-native-edge-catalog"),
                DeclarationHandle.Create(Prefix + "native_f2_native_edge_catalog"),
                H("Catalog Equals Actual Native Edges on the Full F2 Domain"),
                StatementSource.FromAuthor(CatalogFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For m at least four and every raw undirected edge e, F2NativeEdge(m,e) "
                    + "holds exactly when e is the a or b edge at an actual F2Domain vertex. "
                    + "Forward membership uses the actual core and supplier domains of each "
                    + "cataloged circle. Reverse membership uses the earned complete core "
                    + "circle partition or the earned complete supplier gap-circle partition. "
                    + "Gap zero of a remaining supplier lies in the core by the exact "
                    + "contact intersection; every other gap is already in the new catalog."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-f2-hamiltonian-cycle-with-native-edge-inventory"),
                DeclarationHandle.Create(Prefix + "native_f2_hamiltonian_cycle_with_native_edge_inventory"),
                H("One Hamilton Cycle Retains Exactly the Uncut Actual Native Edges"),
                StatementSource.FromAuthor(InventoryFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For m at least four, one actual Hamilton cycle w on F2Domain has the "
                    + "following exact law simultaneously for every actual vertex x in that "
                    + "domain and both native generators g=a,b: its raw edge from x to xg "
                    + "belongs to w precisely when it is outside F2DeletedEdge. The actual "
                    + "coordinate distinction c≠a,b excludes every T/E seam from these "
                    + "native edges. Combining that fact and the exact native catalog "
                    + "bridge with the complete closed inventory eliminates the seam "
                    + "alternative. The certificate also retains the full raw-edge iff, "
                    + "so native retention, every actual seam and Hamiltonicity concern "
                    + "the same witness."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "This exact native edge criterion supports subsequent literal-word legality. "
                + "It does not yet locate the additional six v-marked cuts or prove the five "
                + "J2 words are complete components; those remain separate obligations.")))));

    private static Formula CatalogFormula()
    {
        Formula m = F.Id("m"), e = F.Id("e"), x = F.Id("x"), g = F.Id("g");
        Formula actual = Some("x", Call("Configuration", m), Some("g", Call("Configuration", m),
            And(Call("F2Domain", m, x), And(Native(m, g),
                Eq(e, Call("Sym2Pair", x, Call("Mul", x, g)))))));
        return Disp(All("m", Call("Nat"), Implies(Le(D(4), m),
            All("e", Call("Sym2", Call("Configuration", m)),
                new Formula.Logic(Call("F2NativeEdge", m, e), FormulaLogicOperator.Iff, actual)))));
    }

    private static Formula InventoryFormula()
    {
        Formula m = F.Id("m"), b = F.Id("base"), w = F.Id("w"), x = F.Id("x"), g = F.Id("g");
        Formula domain = Call("F2Domain", m), edge = Call("Sym2Pair", x, Call("Mul", x, g));
        Formula inventory = All("x", Call("Configuration", m), All("g", Call("Configuration", m),
            Implies(Call("F2Domain", m, x), Implies(Native(m, g),
                new Formula.Logic(Call("Member", edge, Call("RawEdges", w)),
                    FormulaLogicOperator.Iff, new Formula.Not(Call("F2DeletedEdge", m, edge)))))));
        Formula e = F.Id("e");
        Formula rawInventory = All("e", Call("Sym2", Call("Configuration", m)),
            new Formula.Logic(Call("Member", e, Call("RawEdges", w)), FormulaLogicOperator.Iff,
                new Formula.Logic(And(Call("F2NativeEdge", m, e),
                    new Formula.Not(Call("F2DeletedEdge", m, e))), FormulaLogicOperator.Or,
                    Call("F2Seam", m, e))));
        return Disp(All("m", Call("Nat"), Implies(Le(D(4), m),
            Some("base", Call("Vertices", domain), Some("w", Call("Walk", Call("domainGraph", domain), b, b),
                And(Call("IsHamiltonianCycle", w), And(rawInventory, inventory)))))));
    }

    private static Formula Native(Formula m, Formula g) =>
        new Formula.Logic(Eq(g, Call("a", m)), FormulaLogicOperator.Or, Eq(g, Call("b", m)));
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
            : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Some(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
}
