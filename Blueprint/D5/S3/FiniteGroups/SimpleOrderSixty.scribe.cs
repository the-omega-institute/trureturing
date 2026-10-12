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
                        + "any geometric realization.")),
                    Paragraph(Text("For the concrete central quotient in CFMP section 124, take "
                        + "G = Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) and "
                        + "Q = Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 5). "
                        + "The latter is definitionally G modulo Subgroup.center G; its projection "
                        + "is QuotientGroup.mk' (Subgroup.center G). Thus the group supplied to "
                        + "smallSimpleOrder60EquivAlt5 is this actual quotient Q. The field is "
                        + "ZMod 5, with primality of five supplying its field instance, and the "
                        + "matrix index type is Fin 2.")),
                    Paragraph(Text("Use the original matrices u = [[0,1],[4,1]] and "
                        + "v = [[1,1],[0,1]], both of determinant one. Preserve the words "
                        + "ell = v^(-1) u^2, h = v^2 u, s = u^(-2) v, "
                        + "t = u^(-3) v u and k = v u^3 in this multiplication order. "
                        + "Matrix multiplication over ZMod 5 gives ell = [[0,1],[4,0]], "
                        + "h = [[3,3],[4,1]], uv = ell, ell^2 = -I, h^3 = I, "
                        + "h != I, u^3 = -I and v^5 = I. Since -I != I, ell has "
                        + "order four; h has order three. These are orders in G.")),
                    Paragraph(Text("The generating subgroup contains v and ell = uv. "
                        + "Conjugating v^(-1) by ell gives the lower transvection "
                        + "[[1,0],[1,1]]. Powers of v and this conjugate give every upper "
                        + "and lower transvection, since every element of ZMod 5 is the "
                        + "image of an integer. Apply Matrix.SL2.transvection_induction with "
                        + "the predicate of belonging to the subgroup: its multiplication "
                        + "and transvection hypotheses are exactly these subgroup membership "
                        + "facts. Consequently u and v generate all of G, without assuming "
                        + "generation as input.")),
                    Paragraph(Text("For K generated by s, t and k, the matrix identities "
                        + "k = -v, k^5 = -I and k^6 = v put v in K. The identity "
                        + "u = (s v^(-1)) k^5 then puts u in K, so the preceding "
                        + "generation argument gives K = G. The generator t is retained "
                        + "in the definition of K even though s and k already suffice "
                        + "for this conclusion.")),
                    Paragraph(Text("To establish the cardinality hypothesis, identify G with "
                        + "the kernel of the determinant homomorphism on GL(2,ZMod 5), "
                        + "using Matrix.SpecialLinearGroup.toGL and its injectivity. "
                        + "Matrix.card_GL_field gives (25-1)(25-5) = 480 elements of GL; "
                        + "Matrix.GeneralLinearGroup.det_surjective identifies its quotient "
                        + "by the determinant kernel with the four field units. "
                        + "Subgroup.card_eq_card_quotient_mul_card_subgroup therefore gives "
                        + "|G| = 120, the same 24 times 5 count as the nonzero-first-column "
                        + "argument in the original construction.")),
                    Paragraph(Text("Matrix.SpecialLinearGroup.mem_center_iff describes the "
                        + "center by scalar matrices rI with r^2 = 1. Over ZMod 5 these "
                        + "are exactly I and -I, which are distinct, so the center has "
                        + "cardinality two. The same quotient cardinality formula gives "
                        + "|Q| = 60. Matrix.ProjectiveSpecialLinearGroup.rank_two_simple' "
                        + "supplies simplicity with the field witness a = 2: a != 0 and "
                        + "a^2 != 1. Noncommutativity is also checked on this quotient: "
                        + "(uv)^(-1)(vu) equals neither I nor -I, so the images of u "
                        + "and v do not commute. Finiteness, cardinality sixty, simplicity "
                        + "and noncommutativity are thus supplied for the exact carrier Q.")),
                    Paragraph(Text("Applying Atlas.GroupTheory.smallSimpleOrder60EquivAlt5 "
                        + "to Q now constructs Q multiplicatively equivalent to "
                        + "alternatingGroup (Fin 5). This is the unmarked group identification "
                        + "asserted in section 124. It does not choose images of u and v. "
                        + "An identification of this quotient pairing with the displayed "
                        + "section 123 pair ((345),(13524)) would require a separate "
                        + "simultaneous generator correspondence, preserving the reversal "
                        + "between function composition and right actions.")),
                    Paragraph(Text("The application establishes matrix relations, generation, "
                        + "K = G and the central quotient group identification. Group orders "
                        + "and element orders alone do not construct the actual face pairings, "
                        + "edge first returns, link charts or normal fan quotients. Actual "
                        + "edge degrees, the full surface and its genus, local ramification "
                        + "and a twelve/nine hyperbolic metric require their corresponding "
                        + "geometric arguments. In particular the six/nine golden lengths "
                        + "are not asserted to solve the twelve/nine metric equations. "
                        + "This is an application of existing algebraic results, with no "
                        + "claim of a new group theorem or geometric completion."))),
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
