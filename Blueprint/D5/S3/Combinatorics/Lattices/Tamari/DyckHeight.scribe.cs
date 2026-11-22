using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Lattices.Tamari;

internal sealed class DyckHeightDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Lattices/Tamari/DyckHeight.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dyck height dominance has a unique coatom in the ranks with two Tamari coatoms.",
        H("Dyck paths ordered by prefix height"),
        Blocks(
            Describe.Lean(DescribeId.Create("dyck-paths"),
                DeclarationHandle.Create(Owner + "DyckPaths"), H("Dyck paths of fixed semilength"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A DyckPaths(n) value contains a Mathlib DyckWord and a proof that its semilength is n."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("dyck-height"),
                DeclarationHandle.Create(Owner + "dyckHeight"), H("Prefix height"),
                StatementSource.FromAuthor(F.Disp(Bind(FormulaQuantifier.ForAll, "p", F.Id("DyckWord"),
                    Bind(FormulaQuantifier.ForAll, "i", NatType, Rel(Call("dyckHeight", F.Id("p"), F.Id("i")),
                    FormulaRelationOperator.Equal, Bin(Call("count", F.Id("U"), Call("take", F.Id("i"),
                    Call("toList", F.Id("p")))), FormulaBinaryOperator.Subtract, Call("count", F.Id("D"),
                    Call("take", F.Id("i"), Call("toList", F.Id("p")))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The height is the integer up-step count minus down-step count in the prefix of length i. The"
                    + " height after the last step is zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("dyck-height-order"),
                DeclarationHandle.Create(Owner + "dyckHeightOrder"), H("Height dominance"),
                StatementSource.FromAuthor(F.Disp(Bind(FormulaQuantifier.ForAll, "n", NatType,
                    Bind(FormulaQuantifier.ForAll, "p", Call("DyckPaths", F.Id("n")),
                    Bind(FormulaQuantifier.ForAll, "q", Call("DyckPaths", F.Id("n")),
                    Logic(Parenthesized(Rel(F.Id("p"), FormulaRelationOperator.LessThanOrEqual, F.Id("q"))),
                    FormulaLogicOperator.Iff, Parenthesized(Bind(FormulaQuantifier.ForAll, "i", NatType,
                    Rel(Call("dyckHeight", Call("val", F.Id("p")), F.Id("i")),
                    FormulaRelationOperator.LessThanOrEqual, Call("dyckHeight", Call("val", F.Id("q")),
                    F.Id("i"))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A path is below another exactly when all its prefix heights are at most those of the other path."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("dyck-order-top"),
                DeclarationHandle.Create(Owner + "dyckOrderTop"), H("The top path"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The mountain with n up-steps followed by n down-steps dominates every path."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("near-mountain"),
                DeclarationHandle.Create(Owner + "nearMountain"), H("The path immediately below the mountain"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Enclose the valleys of the word UDUD in k matching outer pairs of steps. The path then has"
                    + " semilength k + 2."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("near-ne-top"),
                DeclarationHandle.Create(Owner + "near_ne_top"), H("The nearly maximal path is proper"),
                StatementSource.FromAuthor(F.Disp(Bind(FormulaQuantifier.ForAll, "k", NatType,
                    Rel(Call("nearMountain", F.Id("k")), FormulaRelationOperator.NotEqual, Call("top",
                    Call("DyckPaths", Bin(F.Id("k"), FormulaBinaryOperator.Add, D(2)))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At the middle prefix it has fewer up-steps than the mountain."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("no-tamari-dyck-height-iso"),
                DeclarationHandle.Create(Owner + "no_tamari_dyck_height_iso"), H("Height dominance separates at rank three"),
                StatementSource.FromAuthor(F.Disp(Bind(FormulaQuantifier.ForAll, "n", NatType, Logic(Rel(D(3),
                    FormulaRelationOperator.LessThanOrEqual, F.Id("n")), FormulaLogicOperator.Implies,
                    new Formula.Not(Call("Nonempty", Call("OrderIso", Call("Trees", F.Id("n")),
                    Call("DyckPaths", F.Id("n"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every proper Dyck path lies below the same near-mountain path, so there is just one coatom."
                    + " Tamari order at rank n ≥ 3 has two distinct coatoms."))), DescribeRole.Theorem))));

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
