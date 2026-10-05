using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class OrderedSubgroupFactorizationDocument : IScribeDocumentDefinition
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

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One natural allocation table retains both original margins throughout the ordered minimum scan.",
        H("Ordered subgroup-factor allocation"),
        Blocks(Describe.Lean(DescribeId.Create("ordered-natural-allocation-complete"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/Coding/OrderedSubgroupFactorization.ordered_allocation_complete"),
            H("Both original margins from the same prescribed scan"),
            StatementSource.FromAuthor(Disp(Claim())), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For finite row and column carriers, the two supplied lists contain every index. Original demands and capacities are natural numbers with equal total. Starting with a zero table, visit the full row-major rectangle. Each visit computes one pre-update minimum, subtracts it from both residuals, and adds that same value to the actual cell. Zero allocations are visited as well.")),
                Paragraph(Text("In the display, rowResidual and columnResidual are the two residual projections; rowSum and columnSum sum the recorded table over the opposite carrier. tableEntry evaluates that same table. runPrefix folds the same transition from the original demands, original capacities and zero table; grid is the list product and append is list concatenation. sum denotes the complete finite sum of the given margin function.")),
                Paragraph(Text("Every prefix preserves both original conservation equations, has zero unvisited entries, and retains an exhausted endpoint at every visited pair. Residuals do not increase under a visit. Complete-grid coverage gives complementarity at every pair. Equal residual totals then force every row and column residual to zero, yielding both original margins without a supplied feasible table or completion premise. Empty carriers and zero margins remain included.")),
                Paragraph(Text("The native producer uses actual hK, Kh and KhK sets, removes repeated least representatives, sorts them in the prescribed independent group order, and writes each allocation at the least actual intersection element. The source naming convention calls hK right and Kh left; Mathlib calls them left and right respectively. Explicit decidable subgroup membership supplies the computational presentation; it is not claimed as executable extraction from an opaque subgroup predicate.")),
                Paragraph(Text("This retained theorem proves the balanced complete-grid allocation argument. Exact transient applications verify the native least-representative partitions, equicardinal cells, equal distinct coset counts, the original source-balance premise for the same allocation table, least-cell placement, both ordered products, the full zero-inclusive square-cell count, and the equivalence of right-coset constancy with a u_K = q a. These applications introduce no retained companion declarations. Exact transient applications also prove necessity of the original right-coset constancy and double-coset balance from an arbitrary fixed-factor solution. Under right-coset constancy, the second pure equation u_K a = q b u_H is equivalent to the original block balance; together with a u_K = q a this gives the complete pure-algebra criterion. Both mismatch finders reflect actual unequal coefficients or an actual double-coset total mismatch. The inspection succeeds exactly when the original criterion holds, returns this same ordered factor with both products and the complete zero-inclusive square-cell count, and every rejection refutes existence with the fixed factor u_K. These statements include arbitrary finite noncommutative groups, arbitrary subgroups and independent prescribed orders, natural coefficients and b = 0. They do not reject arbitrary strong shift equivalence. The producer retains one computed table per block when assembling its coefficients. Registration is paused and no canonical coverage is asserted."))),
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
        return All(And(rowFinal, And(columnFinal, prefix)),
            B("Row", F.Id("Type")), B("Column", F.Id("Type")),
            B("finiteRows", Call("Fintype", row)), B("finiteColumns", Call("Fintype", column)),
            B("rowEquality", Call("DecidableEq", row)),
            B("columnEquality", Call("DecidableEq", column)),
            B("rows", Call("List", row)), B("columns", Call("List", column)),
            B("allRows", All(Mem(i, rows), B("i", row))),
            B("allColumns", All(Mem(j, columns), B("j", column))),
            B("demand", Call("Arrow", row, F.Id("Nat"))),
            B("capacity", Call("Arrow", column, F.Id("Nat"))),
            B("balanced", Equal(Call("sum", demand), Call("sum", capacity))));
    }
}
