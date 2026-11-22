using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Lattices.Tamari;

internal sealed class BooleanRowsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Lattices/Tamari/BooleanRows.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGeometry/garber2026booleanantichains");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Maximum Boolean antichains of bracketing functions are laminar interval rows.",
        H("Boolean antichains and laminar rows"),
        Blocks(
            Describe.Lean(DescribeId.Create("brackets"),
                DeclarationHandle.Create(Owner + "Brackets"), H("Brackets at the ambient rank"),
                StatementSource.FromAuthor(F.Disp(Bind(FormulaQuantifier.ForAll, "n", NatType,
                    Rel(Call("Brackets", F.Id("n")), FormulaRelationOperator.Equal, Call("BracketingFunctions",
                    Bin(F.Id("n"), FormulaBinaryOperator.Add, D(1))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Brackets(n) denotes brackets on Fin(n + 1)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("is-boolean-family"),
                DeclarationHandle.Create(Owner + "IsBooleanFamily"), H("The Boolean law"),
                StatementSource.FromAuthor(F.Disp(Bind(FormulaQuantifier.ForAll, "L", F.Id("Type"),
                    Seq(Parenthesized(Call("CompleteLattice", F.Id("L"))), Comma, Sp,
                    Bind(FormulaQuantifier.ForAll, "C", Call("Set", F.Id("L")), Logic(Call("IsBooleanFamily",
                    F.Id("C")), FormulaLogicOperator.Iff, Logic(Call("IsAntichain", F.Id("C")),
                    FormulaLogicOperator.And, Logic(new Formula.Not(Rel(Top, FormulaRelationOperator.MemberOf,
                    F.Id("C"))), FormulaLogicOperator.And, Parenthesized(Bind(FormulaQuantifier.ForAll, "S",
                    Call("Set", F.Id("L")), Bind(FormulaQuantifier.ForAll, "T", Call("Set", F.Id("L")),
                    Logic(Logic(Rel(F.Id("S"), FormulaRelationOperator.SubsetOf, F.Id("C")),
                    FormulaLogicOperator.And, Rel(F.Id("T"), FormulaRelationOperator.SubsetOf, F.Id("C"))),
                    FormulaLogicOperator.Implies, Rel(Call("sup", Call("sInf", F.Id("S")), Call("sInf",
                    F.Id("T"))), FormulaRelationOperator.Equal, Call("sInf", Call("inter", F.Id("S"),
                    F.Id("T")))))))))))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("In a complete lattice, C is an antichain excluding top. For every S and T contained in C, the"
                    + " join of their meets is the meet of their intersection. Empty meets equal top. The Boolean law is"
                    + " equation (2.a) in the source."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("boolean-family"),
                DeclarationHandle.Create(Owner + "BooleanFamily"), H("Boolean bracket families"),
                StatementSource.FromAuthor(F.Disp(Bind(FormulaQuantifier.ForAll, "n", NatType,
                    Bind(FormulaQuantifier.ForAll, "C", Call("Set", Call("Brackets", F.Id("n"))),
                    Logic(Call("BooleanFamily", F.Id("C")), FormulaLogicOperator.Iff, Call("IsBooleanFamily",
                    F.Id("C"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("BooleanFamily restricts IsBooleanFamily to sets of Brackets(n)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("laminar"),
                DeclarationHandle.Create(Owner + "Laminar"), H("Laminar interval endpoints"),
                StatementSource.FromAuthor(F.Disp(Bind(FormulaQuantifier.ForAll, "n", NatType,
                    Bind(FormulaQuantifier.ForAll, "A", Seq(Pi, Sp, Parenthesized(Seq(F.Id("s"), Colon,
                    Call("RowIndex", F.Id("n")))), Sp, Call("LeftEndpoint", F.Id("s"))), Logic(Call("Laminar",
                    F.Id("A")), FormulaLogicOperator.Iff, Parenthesized(Bind(FormulaQuantifier.ForAll, "s",
                    Call("RowIndex", F.Id("n")), Bind(FormulaQuantifier.ForAll, "t", Call("RowIndex",
                    F.Id("n")), Logic(Logic(Rel(Call("val", F.Id("s")), FormulaRelationOperator.LessThan,
                    Call("val", F.Id("t"))), FormulaLogicOperator.And, Rel(Call("val",
                    new Formula.Apply(F.Id("A"), [F.Id("t")])), FormulaRelationOperator.LessThanOrEqual,
                    Call("val", F.Id("s")))), FormulaLogicOperator.Implies, Rel(Call("val",
                    new Formula.Apply(F.Id("A"), [F.Id("t")])), FormulaRelationOperator.LessThanOrEqual,
                    Call("val", new Formula.Apply(F.Id("A"), [F.Id("s")])))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If s is earlier than t and the interval ending at t reaches s, that interval contains the"
                    + " interval ending at s."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("boolean-row-family-iff-laminar"),
                DeclarationHandle.Create(Owner + "boolean_rowFamily_iff_laminar"), H("Boolean rows are exactly laminar rows"),
                StatementSource.FromAuthor(F.Disp(Bind(FormulaQuantifier.ForAll, "n", NatType,
                    Bind(FormulaQuantifier.ForAll, "A", Seq(Pi, Sp, Parenthesized(Seq(F.Id("s"), Colon,
                    Call("RowIndex", F.Id("n")))), Sp, Call("LeftEndpoint", F.Id("s"))),
                    Logic(Call("BooleanFamily", Call("range", Call("rowFamily", F.Id("A")))),
                    FormulaLogicOperator.Iff, Call("Laminar", F.Id("A"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A crossing gives two subfamilies that violate the meet law. For laminar intervals, the largest"
                    + " admissible row endpoint establishes the law."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("boolean-family-maximum"),
                DeclarationHandle.Create(Owner + "booleanFamily_maximum"), H("Maximum cardinality in bracket coordinates"),
                StatementSource.FromAuthor(F.Disp(Bind(FormulaQuantifier.ForAll, "n", NatType,
                    Call("IsGreatest", Seq(OpenBrace, F.Id("k"), Mid, Bind(FormulaQuantifier.Exists, "C",
                    Call("Set", Call("Brackets", F.Id("n"))), Logic(Call("BooleanFamily", F.Id("C")),
                    FormulaLogicOperator.And, Rel(Call("ncard", F.Id("C")), FormulaRelationOperator.Equal,
                    F.Id("k")))), CloseBrace), F.Id("n"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each non-top bracket has a proper fixed coordinate. Distinct members of a Boolean family cannot"
                    + " share such a coordinate. Singleton intervals attain n."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("maximum-boolean-iff-laminar-rows"),
                DeclarationHandle.Create(Owner + "maximum_boolean_iff_laminar_rows"), H("The maximum Boolean families"),
                StatementSource.FromAuthor(F.Disp(Bind(FormulaQuantifier.ForAll, "n", NatType,
                    Bind(FormulaQuantifier.ForAll, "C", Call("Set", Call("Brackets", F.Id("n"))),
                    Logic(Parenthesized(Logic(Call("BooleanFamily", F.Id("C")), FormulaLogicOperator.And,
                    Rel(Call("ncard", F.Id("C")), FormulaRelationOperator.Equal, F.Id("n")))),
                    FormulaLogicOperator.Iff, Parenthesized(Bind(FormulaQuantifier.Exists, "A", Seq(Pi, Sp,
                    Parenthesized(Seq(F.Id("s"), Colon, Call("RowIndex", F.Id("n")))), Sp, Call("LeftEndpoint",
                    F.Id("s"))), Logic(Call("Laminar", F.Id("A")), FormulaLogicOperator.And, Rel(F.Id("C"),
                    FormulaRelationOperator.Equal, Call("range", Call("rowFamily", F.Id("A")))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At equality each proper endpoint occurs once, and the bracket is forced to be constant on one"
                    + " interval. The Boolean condition becomes laminarity."))), DescribeRole.Theorem))));

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

    private static Formula Top => Seq(Operatorname, Grp(F.Id("top")));
}
