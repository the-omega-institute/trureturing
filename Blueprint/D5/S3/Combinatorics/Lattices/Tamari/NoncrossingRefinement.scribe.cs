using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Lattices.Tamari;

internal sealed class NoncrossingRefinementDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Lattices/Tamari/NoncrossingRefinement.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Noncrossing refinement has more atoms than Tamari order from rank three.",
        H("Noncrossing partitions in refinement order"),
        Blocks(
            Describe.Lean(DescribeId.Create("partitions"),
                DeclarationHandle.Create(Owner + "Partitions"), H("Partitions of the ordered ground set"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Partitions(n) is the Mathlib Finpartition of the universal Fin(n) set. Adding one to each"
                    + " element identifies its ground order with the ordered set from 1 to n."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("shares"),
                DeclarationHandle.Create(Owner + "Shares"), H("Membership in one block"),
                StatementSource.FromAuthor(F.Disp(Bind(FormulaQuantifier.ForAll, "n", NatType,
                    Bind(FormulaQuantifier.ForAll, "P", Call("Partitions", F.Id("n")),
                    Bind(FormulaQuantifier.ForAll, "x", Call("Fin", F.Id("n")), Bind(FormulaQuantifier.ForAll,
                    "y", Call("Fin", F.Id("n")), Logic(Call("Shares", F.Id("P"), F.Id("x"), F.Id("y")),
                    FormulaLogicOperator.Iff, Parenthesized(Rel(F.Id("y"), FormulaRelationOperator.MemberOf,
                    Call("part", F.Id("P"), F.Id("x"))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Shares(P, x, y) means y belongs to the block of the partition P that contains x."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("is-noncrossing"),
                DeclarationHandle.Create(Owner + "IsNoncrossing"), H("The noncrossing condition"),
                StatementSource.FromAuthor(F.Disp(Bind(FormulaQuantifier.ForAll, "n", NatType,
                    Bind(FormulaQuantifier.ForAll, "P", Call("Partitions", F.Id("n")),
                    Logic(Call("IsNoncrossing", F.Id("P")), FormulaLogicOperator.Iff,
                    new Formula.Not(Parenthesized(Bind(FormulaQuantifier.Exists, "a", Call("Fin", F.Id("n")),
                    Bind(FormulaQuantifier.Exists, "b", Call("Fin", F.Id("n")), Bind(FormulaQuantifier.Exists,
                    "c", Call("Fin", F.Id("n")), Bind(FormulaQuantifier.Exists, "d", Call("Fin", F.Id("n")),
                    Logic(Rel(F.Id("a"), FormulaRelationOperator.LessThan, F.Id("b")),
                    FormulaLogicOperator.And, Logic(Rel(F.Id("b"), FormulaRelationOperator.LessThan,
                    F.Id("c")), FormulaLogicOperator.And, Logic(Rel(F.Id("c"),
                    FormulaRelationOperator.LessThan, F.Id("d")), FormulaLogicOperator.And,
                    Logic(Call("Shares", F.Id("P"), F.Id("a"), F.Id("c")), FormulaLogicOperator.And,
                    Logic(Call("Shares", F.Id("P"), F.Id("b"), F.Id("d")), FormulaLogicOperator.And,
                    new Formula.Not(Call("Shares", F.Id("P"), F.Id("a"), F.Id("b"))))))))))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("There are no four increasing elements alternating between two distinct blocks."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("noncrossing-partitions"),
                DeclarationHandle.Create(Owner + "NoncrossingPartitions"), H("Noncrossing partitions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Restrict the finite partition carrier to IsNoncrossing and retain the Mathlib refinement order."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nc-order-bot"),
                DeclarationHandle.Create(Owner + "ncOrderBot"), H("The least partition"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The partition into singletons is noncrossing and is the lower bound in refinement order."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nc-order-top"),
                DeclarationHandle.Create(Owner + "ncOrderTop"), H("The greatest partition"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The one-block partition is noncrossing and is the upper bound in refinement order."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("no-tamari-noncrossing-iso"),
                DeclarationHandle.Create(Owner + "no_tamari_noncrossing_iso"), H("Noncrossing refinement separates at rank three"),
                StatementSource.FromAuthor(F.Disp(Bind(FormulaQuantifier.ForAll, "n", NatType, Logic(Rel(D(3),
                    FormulaRelationOperator.LessThanOrEqual, F.Id("n")), FormulaLogicOperator.Implies,
                    new Formula.Not(Call("Nonempty", Call("OrderIso", Call("Trees", F.Id("n")),
                    Call("NoncrossingPartitions", F.Id("n"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every two-element block with all other blocks singletons is an atom. Their number in rank n ≥ 3"
                    + " exceeds the bound of n − 1 for Tamari atoms."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nc-one-subsingleton"),
                DeclarationHandle.Create(Owner + "nc_one_subsingleton"), H("Noncrossing refinement at rank one"),
                StatementSource.FromAuthor(F.Disp(Call("Subsingleton", Call("NoncrossingPartitions", D(1))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On a one-point ground set all partitions coincide."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nc-two-bot-or-top"),
                DeclarationHandle.Create(Owner + "nc_two_bot_or_top"), H("Noncrossing refinement at rank two"),
                StatementSource.FromAuthor(F.Disp(Bind(FormulaQuantifier.ForAll, "P",
                    Call("NoncrossingPartitions", D(2)), Logic(Parenthesized(Rel(F.Id("P"),
                    FormulaRelationOperator.Equal, Bot)), FormulaLogicOperator.Or, Parenthesized(Rel(F.Id("P"),
                    FormulaRelationOperator.Equal, Top)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On a two-point ground set the points are either in separate blocks or together."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nc-two-bot-ne-top"),
                DeclarationHandle.Create(Owner + "nc_two_bot_ne_top"), H("The two partitions at rank two"),
                StatementSource.FromAuthor(F.Disp(Rel(Call("bot", Call("NoncrossingPartitions", D(2))),
                    FormulaRelationOperator.NotEqual, Call("top", Call("NoncrossingPartitions", D(2)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The partition into singletons and the one-block partition differ on whether the two points share"
                    + " a block."))), DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] values) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. values]);

    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula domain, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(name), domain, body);

    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);

    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(left, op, right);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula NatType => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Top => Seq(Operatorname, Grp(F.Id("top")));

    private static Formula Bot => Perp;
}
