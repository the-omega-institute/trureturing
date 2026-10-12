using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Transportation;

internal sealed class FerrersIntegerRectanglePathsDocument : IScribeDocumentDefinition
{
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Instances(Formula body, params Formula[] instances)
    {
        var items = new List<Formula>();
        foreach (var instance in instances)
            items.AddRange([OpenBracket, instance, CloseBracket, Comma, Sp]);
        items.Add(body);
        return Seq([.. items]);
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonnegative integer tables with nested legal row neighborhoods have finite legal unit rectangle paths.",
        H("Integer rectangle paths with structural zeros"),
        Blocks(
            Definition("supported", "Legal support", "Supported", SupportDefinition(),
                "Supported(E,P) means that P(i,j) is zero whenever E(i,j) is false, for every row i and column j."),
            Definition("same-margins", "Complete row and column margins", "SameMargins", MarginsDefinition(),
                "rowSum(P,i) is the sum of P(i,j) over every column j; columnSum(P,j) is the sum of P(i,j) over every row i. SameMargins(P,Q) requires equality of each of these complete finite sums."),
            Definition("unit-swap", "A total natural-number rectangle update", "unitSwap", SwapDefinition(),
                "In the formula, value evaluates a function at its displayed arguments, ite selects its second argument when its first argument holds and its third otherwise, and NatSub is subtraction truncated at zero. In row i, unitSwap(P,i,l,j,k) subtracts one at column j and adds one at column k; in row l it subtracts one at k and adds one at j; other rows are unchanged. The row-i case has priority when i equals l, and each row's subtraction column has priority when j equals k. The legal-step relation below requires distinct rows and columns and positive donors, so neither overlap nor truncation occurs in a legal step."),
            Definition("rectangle-step", "A legal unit rectangle step", "RectangleStep", StepDefinition(),
                "RectangleStep(E,P,P') holds when there are distinct rows i and l and distinct columns j and k such that all four corners satisfy E, both P(i,j) and P(l,k) are positive, and P' is exactly unitSwap(P,i,l,j,k)."),
            Describe.Lean(DescribeId.Create("ferrers-integer-rectangle-connected"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/Transportation/FerrersIntegerRectanglePaths.ferrers_integer_rectangle_connected"),
            H("Every intermediate table preserves the same margins and legal support"),
            StatementSource.FromAuthor(Disp(Claim())), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Rows and columns are arbitrary finite carriers. Rows have a linear order, and the allowed neighbors of a row are contained in those of every later row. Entries are natural numbers. Supported means that every forbidden cell is zero; SameMargins means equality of every complete row sum and every complete column sum.")),
                Paragraph(Text("FeasibleRectanglePath denotes the reflexive transitive closure from P to Q of the relation on tables A and B requiring RectangleStep(E,A,B), Supported(E,B), and SameMargins(B,Q). A RectangleStep chooses distinct rows i and l and distinct columns j and k, requires all four corners to be legal and both donor entries A(i,j) and A(l,k) to be positive, and performs the actual update subtracting one from those donors and adding one to A(i,k) and A(l,j). Thus the result is a finite sequence of tables, not merely a signed spanning identity.")),
                Paragraph(Text("At the first unmatched row, equal row totals provide a surplus column and a deficit column. Equal column totals and equality of all earlier rows provide a later donor whose deficit-column entry exceeds its target entry. Nested neighborhoods make the fourth corner legal. The current row's total positive excess decreases by one; the donor row's total positive excess does not increase. Strong induction on the total natural-number excess constructs a finite path. No positive-margin or interior assumption is needed; empty carriers and zero margins are included.")),
                Paragraph(Text("For a board obtained by removing one rectangular block, place the restricted rows before the unrestricted rows. Their neighborhoods are the allowed column complement and the full column set, so the theorem applies. In the five-mode two-window board, order L and B before 0, M and H; the two restricted rows cannot meet columns H and B. This gives the required nested neighborhoods of the twenty-one legal cells.")),
                Paragraph(Text("An integer table of positive total mass becomes a rational probability table after division by that same total. Two supported rational probability tables on the same finite board with nested legal row neighborhoods, equal complete row and column margins, and a common positive denominator D inherit an integer path after scaling by D; normalizing every step by D preserves their common margins and structural zeros. This application is a mathematical parameter correspondence. The Lean theorem here quantifies over natural tables, and does not establish a finite path for arbitrary real tables, the twelve-dimensional real linear kernel, the four-dimensional saturated fiber, or a physical operation on an observer's history.")),
                Paragraph(Text("Rectangle connectivity belongs to classical transportation and Markov-basis mathematics. This is a direct formal construction for nested legal neighborhoods. The adjacent KTV fixed-margin connectivity development at commit 15b5f47c9ac833bfdf99b8b29374af7a678ef4bc uses Boolean entries on the complete board and has no structural-zero predicate; it does not supply this arbitrary-multiplicity restricted-board statement. No mathematical originality is claimed."))),
            DescribeRole.Theorem))));

    private static DocumentBlock Definition(string id, string title, string declaration,
        Formula statement, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(
            "D5/S3/Combinatorics/Transportation/FerrersIntegerRectanglePaths." + declaration),
            H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Table(Formula row, Formula column) =>
        Call("Arrow", row, Call("Arrow", column, F.Id("Nat")));

    private static Formula RelationType(Formula row, Formula column) =>
        Call("Arrow", row, Call("Arrow", column, F.Id("Prop")));

    private static Formula Carriers(Formula body) =>
        All(body, B("Row", F.Id("Type")), B("Column", F.Id("Type")));

    private static Formula SupportDefinition()
    {
        Formula row = F.Id("Row"), column = F.Id("Column");
        Formula e = F.Id("E"), p = F.Id("P"), i = F.Id("i"), j = F.Id("j");
        Formula body = All(Imp(new Formula.Not(Call("value", e, i, j)),
            Equal(Call("value", p, i, j), F.D(0))), B("i", row), B("j", column));
        return Carriers(All(new Formula.Logic(Call("Supported", e, p),
            FormulaLogicOperator.Iff, body), B("E", RelationType(row, column)),
            B("P", Table(row, column))));
    }

    private static Formula MarginsDefinition()
    {
        Formula row = F.Id("Row"), column = F.Id("Column");
        Formula p = F.Id("P"), q = F.Id("Q"), i = F.Id("i"), j = F.Id("j");
        Formula body = And(
            All(Equal(Call("rowSum", p, i), Call("rowSum", q, i)), B("i", row)),
            All(Equal(Call("columnSum", p, j), Call("columnSum", q, j)), B("j", column)));
        return Carriers(Instances(All(new Formula.Logic(Call("SameMargins", p, q),
            FormulaLogicOperator.Iff, body), B("P", Table(row, column)),
            B("Q", Table(row, column))), Call("Fintype", row), Call("Fintype", column)));
    }

    private static Formula SwapDefinition()
    {
        Formula row = F.Id("Row"), column = F.Id("Column");
        Formula p = F.Id("P"), i = F.Id("i"), l = F.Id("l");
        Formula j = F.Id("j"), k = F.Id("k"), a = F.Id("a"), b = F.Id("b");
        Formula cell = Call("value", p, a, b);
        Formula smaller = Call("NatSub", cell, F.D(1));
        Formula larger = new Formula.Binary(cell, FormulaBinaryOperator.Add, F.D(1));
        Formula first = Call("ite", Equal(b, j), smaller, Call("ite", Equal(b, k), larger, cell));
        Formula second = Call("ite", Equal(b, k), smaller, Call("ite", Equal(b, j), larger, cell));
        Formula body = Equal(Call("value", Call("unitSwap", p, i, l, j, k), a, b),
            Call("ite", Equal(a, i), first, Call("ite", Equal(a, l), second, cell)));
        return Carriers(Instances(All(body, B("P", Table(row, column)),
            B("i", row), B("l", row), B("j", column), B("k", column),
            B("a", row), B("b", column)), Call("LinearOrder", row), Call("DecidableEq", column)));
    }

    private static Formula StepDefinition()
    {
        Formula row = F.Id("Row"), column = F.Id("Column");
        Formula e = F.Id("E"), p = F.Id("P"), next = F.Id("Pnext");
        Formula i = F.Id("i"), l = F.Id("l"), j = F.Id("j"), k = F.Id("k");
        Formula body = And(new Formula.Relation(i, FormulaRelationOperator.NotEqual, l),
            And(new Formula.Relation(j, FormulaRelationOperator.NotEqual, k),
            And(Call("value", e, i, j), And(Call("value", e, i, k),
            And(Call("value", e, l, j), And(Call("value", e, l, k),
            And(new Formula.Relation(F.D(0), FormulaRelationOperator.LessThan, Call("value", p, i, j)),
            And(new Formula.Relation(F.D(0), FormulaRelationOperator.LessThan, Call("value", p, l, k)),
                Equal(next, Call("unitSwap", p, i, l, j, k))))))))));
        Formula corners = new Formula.BindMany(FormulaQuantifier.Exists,
            [B("i", row), B("l", row), B("j", column), B("k", column)], body);
        return Carriers(Instances(All(new Formula.Logic(Call("RectangleStep", e, p, next),
            FormulaLogicOperator.Iff, corners), B("E", RelationType(row, column)),
            B("P", Table(row, column)), B("Pnext", Table(row, column))),
            Call("LinearOrder", row), Call("DecidableEq", column)));
    }

    private static Formula Claim()
    {
        Formula row = F.Id("Row"), column = F.Id("Column");
        Formula e = F.Id("E"), p = F.Id("P"), q = F.Id("Q");
        Formula i = F.Id("i"), l = F.Id("l"), j = F.Id("j");
        Formula nested = All(Imp(Le(i, l), All(Imp(Call("value", e, i, j),
            Call("value", e, l, j)), B("j", column))), B("i", row), B("l", row));
        Formula hypotheses = And(nested, And(Call("Supported", e, p),
            And(Call("Supported", e, q), Call("SameMargins", p, q))));
        Formula table = Call("Arrow", row, Call("Arrow", column, F.Id("Nat")));
        return All(Instances(All(Imp(hypotheses, Call("FeasibleRectanglePath", e, p, q)),
            B("E", Call("Arrow", row, Call("Arrow", column, F.Id("Prop")))),
            B("P", table), B("Q", table)),
            Call("Fintype", row), Call("Fintype", column),
            Call("LinearOrder", row), Call("DecidableEq", column)),
            B("Row", F.Id("Type")), B("Column", F.Id("Type")));
    }
}
