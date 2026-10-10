using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Transportation;

internal sealed class OrderedMarginAllocationDocument : IScribeDocumentDefinition
{
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Or, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Mem(Formula value, Formula collection) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, collection);
    private static Formula Instances(Formula body, params Formula[] instances)
    {
        var items = new List<Formula>();
        foreach (var instance in instances)
            items.AddRange([OpenBracket, instance, CloseBracket, Comma, Sp]);
        items.Add(body);
        return Seq([.. items]);
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One ordered natural allocation constructs both original margins without a feasible-table premise.",
        H("Ordered natural margin allocation"),
        Blocks(Describe.Lean(DescribeId.Create("ordered-natural-allocation-complete"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/Transportation/OrderedMarginAllocation.ordered_allocation_complete"),
            H("Both original margins from the same prescribed scan"),
            StatementSource.FromAuthor(Disp(Claim())), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For finite row and column carriers, the two supplied lists contain every index. Original demands and capacities are natural numbers with equal total. Starting with a zero table, visit the full row-major rectangle. Each visit computes one pre-update minimum, subtracts it from both residuals, and adds that same value to the actual cell. Zero allocations are visited as well.")),
                Paragraph(Text("In the display, rowResidual and columnResidual are the two residual projections; rowSum and columnSum sum the recorded table over the opposite carrier. tableEntry evaluates that same table. runPrefix folds the same transition from the original demands, original capacities and zero table; grid is the list product and append is list concatenation. sum denotes the complete finite sum of the given margin function.")),
                Paragraph(Text("Every prefix preserves both original conservation equations, has zero unvisited entries, and retains an exhausted endpoint at every visited pair. Residuals do not increase under a visit. Complete-grid coverage gives complementarity at every pair. Equal residual totals then force every row and column residual to zero, yielding both original margins without a supplied feasible table or completion premise. Empty carriers and zero margins remain included.")),
                Paragraph(Text("The subgroup-factorization construction consumes this same allocation theorem for every actual double-coset rectangle, with original coefficient demands and original constant capacities."))),
            DescribeRole.Theorem))));

    private static Formula Claim()
    {
        Formula row = F.Id("Row"), column = F.Id("Column");
        Formula rows = F.Id("rows"), columns = F.Id("columns");
        Formula demand = F.Id("demand"), capacity = F.Id("capacity");
        Formula i = F.Id("i"), j = F.Id("j"), cell = F.Id("cell");
        Formula past = F.Id("past"), future = F.Id("future");
        Formula state = Call("orderedAllocation", rows, columns, demand, capacity);
        Formula t = Call("runPrefix", past, demand, capacity);
        Formula r = Call("rowResidual", t, i), c = Call("columnResidual", t, j);
        Formula rowLedger = All(Equal(Add(r, Call("rowSum", t, i)),
            Call("value", demand, i)), B("i", row));
        Formula columnLedger = All(Equal(Add(c, Call("columnSum", t, j)),
            Call("value", capacity, j)), B("j", column));
        Formula exhausted = All(Imp(Mem(cell, past), Or(
            Equal(Call("rowResidual", t, Call("first", cell)), F.D(0)),
            Equal(Call("columnResidual", t, Call("second", cell)), F.D(0)))),
            B("cell", Call("Product", row, column)));
        Formula unvisited = All(Imp(new Formula.Not(Mem(cell, past)),
            Equal(Call("tableEntry", t, cell), F.D(0))),
            B("cell", Call("Product", row, column)));
        Formula bounded = And(
            All(Le(r, Call("value", demand, i)), B("i", row)),
            All(Le(c, Call("value", capacity, j)), B("j", column)));
        Formula prefix = All(Imp(Equal(Call("grid", rows, columns),
            Call("append", past, future)), And(rowLedger, And(columnLedger,
            And(exhausted, And(unvisited, bounded))))),
            B("past", Call("List", Call("Product", row, column))),
            B("future", Call("List", Call("Product", row, column))));
        Formula rowFinal = All(And(
            Equal(Call("rowResidual", state, i), F.D(0)),
            Equal(Call("rowSum", state, i), Call("value", demand, i))), B("i", row));
        Formula columnFinal = All(And(
            Equal(Call("columnResidual", state, j), F.D(0)),
            Equal(Call("columnSum", state, j), Call("value", capacity, j))), B("j", column));
        Formula hypotheses = And(All(Mem(i, rows), B("i", row)),
            And(All(Mem(j, columns), B("j", column)),
                Equal(Call("sum", demand), Call("sum", capacity))));
        return All(Instances(All(Imp(hypotheses, And(rowFinal, And(columnFinal, prefix))),
            B("rows", Call("List", row)), B("columns", Call("List", column)),
            B("demand", Call("Arrow", row, F.Id("Nat"))),
            B("capacity", Call("Arrow", column, F.Id("Nat")))),
            Call("Fintype", row), Call("Fintype", column),
            Call("DecidableEq", row), Call("DecidableEq", column)),
            B("Row", F.Id("Type")), B("Column", F.Id("Type")));
    }

}
