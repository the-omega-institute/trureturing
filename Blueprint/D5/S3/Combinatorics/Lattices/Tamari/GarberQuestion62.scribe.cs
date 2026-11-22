using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Lattices.Tamari;

internal sealed class GarberQuestion62Document : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Lattices/Tamari/GarberQuestion62.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGeometry/garber2026booleanantichains");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Maximum Boolean antichains have Tamari order with exact comparison boundaries.",
        H("Garber et al. Question 6.2"),
        Blocks(
            Describe.Lean(DescribeId.Create("tamari-dyck-paths"),
                DeclarationHandle.Create(Owner + "TamariDyckPaths"), H("Dyck paths carrying Tamari order"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This carrier contains the same semilength-n Dyck paths as DyckPaths(n)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("tamari-dyck-order"),
                DeclarationHandle.Create(Owner + "tamariDyckOrder"), H("Transported Tamari order"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Compare the trees corresponding to the paths under Mathlib’s fixed-size Dyck-word equivalence,"
                    + " using contextual right-rotation reachability on the trees."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create(Owner + "result"), H("The order and both comparison boundaries"),
                StatementSource.FromAuthor(F.Disp(Bind(FormulaQuantifier.ForAll, "n", NatType, Logic(Rel(D(1),
                    FormulaRelationOperator.LessThanOrEqual, F.Id("n")), FormulaLogicOperator.Implies,
                    Parenthesized(Logic(Call("IsGreatest", Seq(OpenBrace, F.Id("k"), Mid,
                    Bind(FormulaQuantifier.Exists, "C", Call("Set", Call("Trees", Bin(F.Id("n"),
                    FormulaBinaryOperator.Add, D(1)))), Logic(Call("IsBooleanFamily", F.Id("C")),
                    FormulaLogicOperator.And, Rel(Call("ncard", F.Id("C")), FormulaRelationOperator.Equal,
                    F.Id("k")))), CloseBrace), F.Id("n")), FormulaLogicOperator.And, Logic(Call("Nonempty",
                    Call("OrderIso", Call("MaximumFamilies", Call("Trees", Bin(F.Id("n"),
                    FormulaBinaryOperator.Add, D(1))), F.Id("n")), Call("Trees", F.Id("n")))),
                    FormulaLogicOperator.And, Logic(Parenthesized(Logic(Call("Nonempty", Call("OrderIso",
                    Call("MaximumFamilies", Call("Trees", Bin(F.Id("n"), FormulaBinaryOperator.Add, D(1))),
                    F.Id("n")), Call("NoncrossingPartitions", F.Id("n")))), FormulaLogicOperator.Iff,
                    Parenthesized(Rel(F.Id("n"), FormulaRelationOperator.LessThanOrEqual, D(2))))),
                    FormulaLogicOperator.And, Logic(Parenthesized(Logic(Call("Nonempty", Call("OrderIso",
                    Call("MaximumFamilies", Call("Trees", Bin(F.Id("n"), FormulaBinaryOperator.Add, D(1))),
                    F.Id("n")), Call("DyckPaths", F.Id("n")))), FormulaLogicOperator.Iff,
                    Parenthesized(Rel(F.Id("n"), FormulaRelationOperator.LessThanOrEqual, D(2))))),
                    FormulaLogicOperator.And, Call("Nonempty", Call("OrderIso", Call("MaximumFamilies",
                    Call("Trees", Bin(F.Id("n"), FormulaBinaryOperator.Add, D(1))), F.Id("n")),
                    Call("TamariDyckPaths", F.Id("n"))))))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Garber, Goltermann, Horiatakis, König and Gottesman ask in Question 6.2 of Counting Boolean"
                    + " antichains (2026), “Is the order on Boolean antichains of maximal size in the Tamari lattice"
                    + " equivalent to the Tamari order, the order on non-crossing partitions, or the order on Dyck"
                    + " paths?” For every n ≥ 1 the maximum size in Tamari rank n + 1 is n, and generated lower-set"
                    + " inclusion is order-isomorphic to contextual right rotations at rank n. Noncrossing refinement"
                    + " and Dyck height dominance each give an isomorphic order exactly at n = 1 and n = 2. The Dyck"
                    + " paths with transported Tamari order give an isomorphism for every n ≥ 1. The order of families"
                    + " on arbitrary lattices lies outside the first sentence."))), DescribeRole.Theorem))));

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
