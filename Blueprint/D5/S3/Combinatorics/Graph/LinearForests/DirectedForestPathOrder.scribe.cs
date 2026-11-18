using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.LinearForests;

internal sealed class DirectedForestPathOrderDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/LinearForests/DirectedForestPathOrder.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/tsaban2003permutation");
    private static Formula Name(string name) =>
        new Formula.NamedConstant(FormulaIdentifier.Create(name));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Fiber => Call("ComponentFiber", F.Id("E"), F.Id("A"));
    private static Formula Indices => Call("Fin", Call("card", Fiber));
    private static Formula Enumeration => Call("Equiv", Indices, Fiber);
    private static Formula Adjacent(string enumeration)
    {
        var ei = Call("value", Call("apply", F.Id(enumeration), F.Id("i")));
        var ej = Call("value", Call("apply", F.Id(enumeration), F.Id("j")));
        return All("i", Indices, All("j", Indices,
            Iff(Call("E", ei, ej),
                Eq(Call("add", Call("val", F.Id("i")), D(1)), Call("val", F.Id("j"))))));
    }
    private static Formula Statement() =>
        All("V", Name("Type"),
            Imp(Call("Finite", F.Id("V")),
                All("E", Call("Relation", F.Id("V")),
                    Imp(And(Call("RightUnique", F.Id("E")),
                            And(Call("LeftUnique", F.Id("E")), Call("Acyclic", F.Id("E")))),
                        All("A", Call("Component", F.Id("E")),
                            Ex("e", Enumeration,
                                And(Adjacent("e"),
                                    All("f", Enumeration,
                                        Imp(Adjacent("f"), Eq(F.Id("f"), F.Id("e")))))))))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Each weak component of a finite acyclic partial permutation has a unique exhaustive directed path enumeration, including isolated singletons.",
        H("Unique directed path order of a component"),
        Blocks(Describe.Lean(
            DescribeId.Create("unique-directed-component-path-order"),
            DeclarationHandle.Create(Prefix + "component_path_order"),
            H("Consecutive indices are exactly the directed edges"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromLiterature(Source),
            Blocks(
                Paragraph(Text(
                    "Let V be any finite type. Let E be right-unique, meaning at most one outgoing neighbor, "
                    + "and left-unique, meaning at most one incoming neighbor. Acyclic means that Relation.TransGen E "
                    + "is irreflexive. For every A in Component E, the fiber is literally the subtype "
                    + "{x : V // Quotient.mk (EqvGen.setoid E) x = A}, with no supplied path data or chosen representative. "
                    + "There exists a unique equivalence e from Fin(Nat.card(ComponentFiber E A)) onto that fiber "
                    + "such that E (e i).val (e j).val holds if and only if i.val+1=j.val, for all i and j. "
                    + "The formula expands unique existence as existence together with equality of every competing enumeration.")),
                Paragraph(Text(
                    "The equivalence exhausts the actual component and repeats no vertex. No lower bound on the number "
                    + "of components is assumed. An isolated component has a one-point fiber, its unique enumeration, "
                    + "and no consecutive indices, hence no edge. The empty ambient carrier has no component A.")),
                Paragraph(Text(
                    "The proof reuses DirectedForestCompletion.full_cycle_completion_equiv only to select the "
                    + "already-proved tail of A and its membership, then applies the original path_to_tail lemma "
                    + "to both actual vertices. Reversing those paths and using Mathlib's total_of_right_unique "
                    + "with LeftUnique E as right uniqueness of swap E makes directed reachability total on the fiber. "
                    + "Acyclicity and transitivity make it a strict total order. Mathlib's monoEquivOfFin supplies "
                    + "its increasing finite enumeration.")),
                Paragraph(Text(
                    "An E-edge cannot skip an intermediate reachability position. The first edge of any path from "
                    + "its source is the prescribed successor by right uniqueness; an intermediate path back to "
                    + "the edge's target would then form a nonempty directed cycle. Conversely, split a path between "
                    + "consecutive order positions at its first edge. Its first successor belongs to the same actual fiber. "
                    + "If it differed from the target, its index would lie strictly between consecutive natural numbers. "
                    + "This proves both directions of exact adjacency.")),
                Paragraph(Text(
                    "For uniqueness, compose a competing path enumeration with the inverse of the constructed one. "
                    + "Each consecutive pair maps to a consecutive pair by their two adjacency laws. "
                    + "Mathlib's Fin.strictMono_iff_lt_succ and StrictMono.eq_id show that this self-map of the finite "
                    + "linear order is the identity, hence the two equivalences agree.")),
                Paragraph(Text(
                    "This formalizes the directed path-component clause of the classical partial-permutation picture "
                    + "in Tsaban, Section 1, Lemma 1.1, pages 107–108. The citation supplies mathematical lineage; "
                    + "no literature priority is claimed. Counts and probability laws are separate conclusions."))),
            DescribeRole.Theorem)), []));
}
