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
                StatementSource.FromAuthor(F.Disp(ResultFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Garber, Goltermann, Horiatakis, König and Gottesman ask in Question 6.2 of Counting Boolean"
                    + " antichains (2026), “Is the order on Boolean antichains of maximal size in the Tamari lattice"
                    + " equivalent to the Tamari order, the order on non-crossing partitions, or the order on Dyck"
                    + " paths?” For every n ≥ 1 the maximum size in Tamari rank n + 1 is n, and generated lower-set"
                    + " inclusion is order-isomorphic to contextual right rotations at rank n. Noncrossing refinement"
                    + " and Dyck height dominance each give an isomorphic order exactly at n = 1 and n = 2. The Dyck"
                    + " paths with transported Tamari order give an isomorphism for every n ≥ 1. The order of families"
                    + " on arbitrary lattices lies outside the first sentence."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("garber-et-al-2026-tamari-boolean-antichains"),
                    ResolutionKind.Proved)))));

    private static Formula ResultFormula()
    {
        var rank = F.Id("n");
        var cardinality = F.Id("k");
        var family = F.Id("C");
        var ambientTrees = Call("Trees", Bin(rank, FormulaBinaryOperator.Add, D(1)));
        var maximumFamilies = Call("MaximumFamilies", ambientTrees, rank);
        var possibleSizes = Seq(OpenBrace, Seq(cardinality, Sp, InMacro, Sp, NatType), Sp, Mid, Sp,
            Bind(FormulaQuantifier.Exists, "C", Call("Set", ambientTrees),
                Logic(Call("IsBooleanFamily", family), FormulaLogicOperator.And,
                    Rel(Call("ncard", family), FormulaRelationOperator.Equal, cardinality))), CloseBrace);
        var maximum = Call("IsGreatest", possibleSizes, rank);
        var smallRank = Parenthesized(Rel(rank, FormulaRelationOperator.LessThanOrEqual, D(2)));
        var tamari = IsomorphismExists(maximumFamilies, Call("Trees", rank));
        var refinement = Parenthesized(Logic(
            IsomorphismExists(maximumFamilies, Call("NoncrossingPartitions", rank)),
            FormulaLogicOperator.Iff, smallRank));
        var height = Parenthesized(Logic(
            IsomorphismExists(maximumFamilies, Call("DyckPaths", rank)),
            FormulaLogicOperator.Iff, smallRank));
        var transported = IsomorphismExists(maximumFamilies, Call("TamariDyckPaths", rank));
        var answer = Logic(maximum, FormulaLogicOperator.And,
            Logic(tamari, FormulaLogicOperator.And,
                Logic(refinement, FormulaLogicOperator.And,
                    Logic(height, FormulaLogicOperator.And, transported))));
        return Bind(FormulaQuantifier.ForAll, "n", NatType,
            Logic(Rel(D(1), FormulaRelationOperator.LessThanOrEqual, rank),
                FormulaLogicOperator.Implies, Parenthesized(answer)));
    }

    private static Formula IsomorphismExists(Formula source, Formula target) =>
        Call("Nonempty", Call("OrderIso", source, target));

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
