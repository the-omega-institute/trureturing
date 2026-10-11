using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class SimpleOrderSixtyDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Atlas =
        LibraryNoteRef.Create("D5/L/FiniteGroups/atlas2026simpleordersixty");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite nonabelian simple group of order sixty is multiplicatively "
        + "equivalent to the alternating group on five letters.",
        H("Recognition of Simple Groups of Order Sixty"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("simple-order-sixty-recognition"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SimpleOrderSixty.smallSimpleOrder60EquivAlt5"),
                H("The multiplicative equivalence"),
                StatementSource.FromAuthor(RecognitionType()),
                AssessedProvenance.FromLiterature(Atlas),
                Blocks(
                    Paragraph(Text("The type G and its universe are arbitrary. It carries a group "
                        + "structure, is finite and simple, has cardinality sixty, and is nonabelian. "
                        + "The conclusion is an actual multiplicative equivalence from G to the "
                        + "alternating group on Fin 5. No classifier or prescribed images of "
                        + "generators are assumed. The display gives the function type of the "
                        + "construction: Typeu denotes an arbitrary universe, card is Nat.card, "
                        + "Not is logical negation, and MulEquiv is the type of multiplicative "
                        + "equivalences. The chosen group structure is used throughout.")),
                    Paragraph(Text("Simplicity makes every proper subgroup have index at least five: "
                        + "a smaller nontrivial coset action would embed G into a permutation group "
                        + "of order at most twenty-four. The Sylow two-subgroups have order four, "
                        + "and their number is five or fifteen. The Sylow five-subgroups have order "
                        + "five, and there are six of them.")),
                    Paragraph(Text("Five Sylow two-subgroups give an index-five normalizer. If there "
                        + "are fifteen and their pairwise intersections are trivial, their forty-five "
                        + "nonidentity elements, together with twenty-four from the Sylow "
                        + "five-subgroups, exceed the order of G. Otherwise two distinct Sylow "
                        + "two-subgroups share a nonidentity element t. Both lie in its centralizer, "
                        + "since groups of order four are commutative. That centralizer is proper "
                        + "because the center of a nonabelian simple group is trivial. Its order "
                        + "is a multiple of four strictly larger than four, divides sixty, and "
                        + "is at most twelve. It therefore has order twelve and index five.")),
                    Paragraph(Text("The action on the five cosets is faithful: its normal kernel "
                        + "is trivial or the whole simple group, and the latter would make the "
                        + "coset space a singleton. After choosing five coordinates, compose with "
                        + "the sign homomorphism. A faithful map from a group of order sixty into "
                        + "the two-element sign group is impossible, so the sign is trivial. The "
                        + "coset action thus embeds G into the alternating group on five letters. "
                        + "Both groups have order sixty, making this embedding bijective.")),
                    Paragraph(Text("This is the classical finite-group recognition argument recorded "
                        + "in the cited ATLAS software source. A quotient application must supply "
                        + "its own cardinality, simplicity and noncommutativity proofs. The "
                        + "equivalence here does not identify specified generators or establish "
                        + "any geometric realization."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("index-five-subgroup"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SimpleOrderSixty.subgroup_index_five_of_simple_card_sixty"),
                H("An index-five subgroup"),
                StatementSource.FromAuthor(IndexFiveStatement()),
                AssessedProvenance.FromLiterature(Atlas),
                Blocks(Paragraph(Text("Sylow counting and the centralizer argument construct a "
                    + "subgroup of index five under the same finite, simple, nonabelian and "
                    + "order-sixty hypotheses."))),
                DescribeRole.Theorem))));

    private static Formula RecognitionType()
    {
        var g = F.Id("G");
        Formula body = Call("MulEquiv", g, Call("alternatingGroup", Call("Fin", D(5))));
        body = new Formula.TypeArrow(Call("Not", Call("IsMulCommutative", g)), body);
        body = new Formula.TypeArrow(Equal(Call("card", g), D(6, 0)), body);
        body = new Formula.TypeArrow(Call("IsSimpleGroup", g), body);
        body = new Formula.TypeArrow(Call("Finite", g), body);
        body = new Formula.TypeArrow(Call("Group", g), body);
        return Disp(All("G", F.Id("Typeu"), body));
    }

    private static Formula IndexFiveStatement()
    {
        var g = F.Id("G");
        Formula body = new Formula.BindMany(FormulaQuantifier.Exists,
            [new Formula.BoundVariable(FormulaIdentifier.Create("H"), Call("Subgroup", g))],
            Equal(Call("index", F.Id("H")), D(5)));
        Formula assumptions = And(Call("Group", g), Call("Finite", g),
            Call("IsSimpleGroup", g), Equal(Call("card", g), D(6, 0)),
            Call("Not", Call("IsMulCommutative", g)));
        return Disp(All("G", F.Id("Typeu"),
            new Formula.Logic(assumptions, FormulaLogicOperator.Implies, body)));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), domain)], body);
    private static Formula And(Formula first, params Formula[] rest)
    {
        Formula result = first;
        foreach (Formula next in rest)
            result = new Formula.Logic(result, FormulaLogicOperator.And, next);
        return result;
    }
}
