using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Lattices.Tamari;

internal sealed class MaximumFamiliesDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Lattices/Tamari/MaximumFamilies.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Maximum Boolean antichains carry the next smaller Tamari order.",
        H("The order of maximum Boolean antichains"),
        Blocks(
            Describe.Lean(DescribeId.Create("maximum-families"),
                DeclarationHandle.Create(Owner + "MaximumFamilies"), H("Families of a prescribed cardinality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An element consists of a set C in a complete lattice, a proof of IsBooleanFamily(C), and the"
                    + " equality of its cardinality with the prescribed n."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("maximum-families-order"),
                DeclarationHandle.Create(Owner + "maximumFamiliesOrder"), H("Inclusion of generated lower sets"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A family is below another when the lower set it generates is included in the other generated"
                    + " lower set. The maximal elements recover the generating antichain."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("tamari-complete-lattice"),
                DeclarationHandle.Create(Owner + "tamariCompleteLattice"), H("The lattice on the rotation order"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Transport the bracket infimum back along treeBracketOrderIso. Its partial order is the"
                    + " contextual rotation order."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("maximum-tamari-order-iso"),
                DeclarationHandle.Create(Owner + "maximumTamariOrderIso"), H("The next smaller Tamari order"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Classify maximum families as laminar interval arrays. Comparing their left endpoints gives the"
                    + " order. Reflecting the arrays gives the dual bracket order, and mirroring the trees reverses it"
                    + " again."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("maximum-tamari-card"),
                DeclarationHandle.Create(Owner + "maximumTamari_card"), H("The maximum in Tamari rank n + 1"),
                StatementSource.FromAuthor(F.Disp(Bind(FormulaQuantifier.ForAll, "n", NatType,
                    Call("IsGreatest", Seq(OpenBrace, Seq(F.Id("k"), Sp, InMacro, Sp, NatType), Sp, Mid, Sp,
                    Bind(FormulaQuantifier.Exists, "C", Call("Set", Call("Trees", Bin(F.Id("n"),
                    FormulaBinaryOperator.Add, D(1)))), Logic(Call("IsBooleanFamily", F.Id("C")),
                    FormulaLogicOperator.And, Rel(Call("ncard", F.Id("C")), FormulaRelationOperator.Equal,
                    F.Id("k")))), CloseBrace), F.Id("n"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Transport the bracket cardinality bound and the attaining family along the tree bracket order"
                    + " isomorphism."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("order-iso-atom-card"),
                DeclarationHandle.Create(Owner + "orderIso_atomCard"), H("Atom count is an order invariant"),
                StatementSource.FromAuthor(F.Disp(AtomCardinalityInvariant())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An order isomorphism of orders with bottom induces an equivalence of their atom subtypes."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("tamari-atom-card-le"),
                DeclarationHandle.Create(Owner + "tamari_atom_card_le"), H("Tamari atom bound"),
                StatementSource.FromAuthor(F.Disp(Bind(FormulaQuantifier.ForAll, "n", NatType,
                    Rel(Call("NatCard", Seq(OpenBrace, F.Id("x"), Sp, Mid, Sp, Logic(Rel(F.Id("x"),
                    FormulaRelationOperator.MemberOf, Call("Trees", Bin(F.Id("n"), FormulaBinaryOperator.Add,
                    D(1)))), FormulaLogicOperator.And, Call("IsAtom", F.Id("x"))), CloseBrace)),
                    FormulaRelationOperator.LessThanOrEqual, F.Id("n"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An atom of the bracket order must be a single one-step increase from the identity bracket. In"
                    + " rank n + 1 there are at most n available coordinates."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("tamari-two-coatoms"),
                DeclarationHandle.Create(Owner + "tamari_two_coatoms"), H("Two distinct Tamari coatoms"),
                StatementSource.FromAuthor(F.Disp(Bind(FormulaQuantifier.ForAll, "n", NatType, Logic(Rel(D(2),
                    FormulaRelationOperator.LessThanOrEqual, F.Id("n")), FormulaLogicOperator.Implies,
                    Parenthesized(Bind(FormulaQuantifier.Exists, "a", Call("Trees", Bin(F.Id("n"),
                    FormulaBinaryOperator.Add, D(1))), Bind(FormulaQuantifier.Exists, "b", Call("Trees",
                    Bin(F.Id("n"), FormulaBinaryOperator.Add, D(1))), Logic(Call("IsCoatom", F.Id("a")),
                    FormulaLogicOperator.And, Logic(Call("IsCoatom", F.Id("b")), FormulaLogicOperator.And,
                    Rel(F.Id("a"), FormulaRelationOperator.NotEqual, F.Id("b"))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At n ≥ 2 the bracket coatoms from two different right endpoints transport to distinct coatoms in"
                    + " Trees(n + 1)."))), DescribeRole.Theorem))));

    private static Formula AtomCardinalityInvariant()
    {
        var forall = FormulaQuantifier.ForAll;
        var aType = F.Id("A");
        var bType = F.Id("B");
        var equality = Rel(AtomSubtypeCard("a", aType), FormulaRelationOperator.Equal,
            AtomSubtypeCard("b", bType));
        return Bind(forall, "A", F.Id("Type"),
            Bind(forall, "B", F.Id("Type"),
                Bind(forall, "poA", Call("PartialOrder", aType),
                    Bind(forall, "poB", Call("PartialOrder", bType),
                        Bind(forall, "botA", Call("OrderBot", aType),
                            Bind(forall, "botB", Call("OrderBot", bType),
                                Bind(forall, "e", Call("OrderIso", aType, bType), equality)))))));
    }

    private static Formula AtomSubtypeCard(string name, Formula type) =>
        Call("NatCard", Seq(OpenBrace, F.Id(name), Colon, Sp, type, Sp, Mid, Sp,
            Call("IsAtom", F.Id(name)), CloseBrace));

    private static Formula Call(string name, params Formula[] values) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. values]);

    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula domain, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(name), domain, body);

    private static Formula Bin(Formula left, FormulaBinaryOperator op, Formula right) =>
        new Formula.Binary(left, op, right);

    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);

    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(left, op, right);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula NatType => Seq(Mathbb, Grp(F.Id("N")));
}
