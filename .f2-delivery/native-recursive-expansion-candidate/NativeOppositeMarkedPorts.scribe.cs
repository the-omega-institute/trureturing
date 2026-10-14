using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeOppositeMarkedPortsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeOppositeMarkedPorts.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical protected-label exchange separates the complete native rotation and reversal port tables. The separation is earned from two adjacent independent base positions, not supplied as a recursive-state hypothesis.",
        H("Opposite Native Marked Ports"),
        Blocks(
            Item("native_opposite_ports_disjoint", "All Four Native Port Intersections Are Empty",
                Frame(All("i", Call("Nat"), All("j", Call("Nat"),
                    And(Ne(R(Bar(), "j"), R(F.Id("frame"), "i")),
                    And(Ne(R(Bar(), "j"), L(F.Id("frame"), "i")),
                    And(Ne(L(Bar(), "j"), R(F.Id("frame"), "i")),
                        Ne(L(Bar(), "j"), L(F.Id("frame"), "i")))))))),
                "For every complete frame with at least two selected labels and at least three independent base labels, every natural rotation index i and j gives four unequal native configurations: opposite right versus original right or left, and opposite left versus original right or left. The opposite frame exchanges exactly the protected final selected pair. Its anchor is the protected-label transposition multiplied by the original anchor. This transposition fixes the labels at adjacent base positions k and k plus one. One fixed prefix position forces an intersecting pair of rotations to have identical rotation permutations, contradicting the nontrivial transposition. Two adjacent fixed positions would force an intersecting rotation and reflection to satisfy zero congruent to two modulo m, contradicting m at least five. No Hamiltonian-cycle witness or all-order recursive existence is assumed or asserted."),
            Item("native_opposite_marked_port_injective", "Both Marked Tables Jointly Have Unique Vertices",
                Frame(Call("Injective", Call("TaggedSpecialPort", F.Id("frame"), Bar()))),
                "Under the same explicit selected-count and base-length assumptions, the function indexed by a Boolean order tag and a pair from Fin(k plus one) times Fin(two) is injective. Each tag selects the original frame or its canonical protected-label exchange. Within either table the existing native special-port injection applies; between the tables the newly earned four-way separation applies. Distinct tags therefore cannot silently refer to the same actual native vertex."),
            Item("native_opposite_marked_cuts_disjoint", "The Two Actual Marked Deletion Sets Are Disjoint",
                Frame(Call("Disjoint", Call("MarkedCuts", F.Id("frame")), Call("MarkedCuts", Bar()))),
                "Under those same assumptions, markedCuts of the original frame and markedCuts of its canonical opposite frame have no common undirected edge. Every marked cut joins its literal right and left ports at one index. Equality of two undirected edges would identify the opposite right port with one original endpoint, contradicting the earned separation. This supplies an actual deletion-set invariant for simultaneous path partitions; it does not build those partitions or their common cycle witness."))));

    private static DocumentBlock Item(string name, string title, Formula formula, string meaning) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(meaning))), DescribeRole.Theorem);
    private static Formula Frame(Formula body) => Disp(All("m", Call("Nat"), All("k", Call("Nat"),
        All("frame", Call("SupplyFrame", F.Id("m"), F.Id("k")),
            Implies(And(Call("AtLeast", F.Id("k"), D(2)),
                Call("AtLeast", Call("Length", Call("Base", F.Id("frame"))), D(3))), body)))));
    private static Formula Bar() => Call("OppositeSelectedFrame", F.Id("frame"));
    private static Formula R(Formula frame, string index) => Call("RightPort", frame, F.Id(index));
    private static Formula L(Formula frame, string index) => Call("LeftPort", frame, F.Id(index));
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Ne(Formula a, Formula b) => new Formula.Logic(
        new Formula.Relation(a, FormulaRelationOperator.Equal, b), FormulaLogicOperator.Implies, Call("False"));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
