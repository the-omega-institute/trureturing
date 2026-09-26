using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class SolidPartitionFirstColumnDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SolidPartitionFirstColumn.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/meeussen2004a098052");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The solid partitions of n that extend in exactly four ways to a solid partition of n + 1, and the solid partitions of n + 1 that contain exactly one solid partition of n, are the boxes, so both are counted by the number of ordered factorizations of n, respectively n + 1, into four factors.",
        H("The first columns of A098052 and A098530 are tau_4"),
        Blocks(
            Node("solid", "Solid partitions", SolidFormula(),
                "A solid partition of n is read through its four-dimensional Ferrers diagram: a finite set of n cells of the fourth power of the natural numbers that contains every cell below any of its cells in the coordinatewise order.",
                "IsSolidPartition", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("extensions", "Extensions", ExtensionsFormula(),
                "The number of solid partitions of n + 1 that contain I.",
                "extensions", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("shrinkings", "Shrinkings", ShrinkingsFormula(),
                "The number of solid partitions of n contained in J.",
                "shrinkings", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("column", "The first column of A098052", ColumnFormula(),
                "The number of solid partitions of n that extend in exactly four ways.",
                "a098052FirstColumn", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("shrinkcolumn", "The first column of A098530", ShrinkColumnFormula(),
                "The number of solid partitions of n + 1 that shrink in exactly one way.",
                "a098530FirstColumn", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("tau", "Ordered factorizations into four factors", TauFormula(),
                "A007426: the number of ordered quadruples of natural numbers whose product is n.",
                "tau4", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The first-column conjectures", ClaimFormula(),
                "For every n at least 1 the first column of A098052 at n is the number of ordered factorizations of n into four factors, and the first column of A098530 at n is that number for n + 1.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Proof of the conjectures", Disp(F.Id("claim")),
                "For positive v the box of cells c with c_i < v_i for every i is a lower set with the product of the v_i cells, and it determines v; so boxes of n cells correspond to ordered factorizations of n. The solid partitions of n + 1 containing a box are exactly the box with one of the four axis cells v_i e_i added: every cell strictly below the new cell lies in the box, which forces the new cell onto an axis at distance v_i. A nonempty lower set that is not a box has a fifth extension: with v_i one more than its largest i-th coordinate the four axis cells can be added, and the cell of least coordinate sum in the box of v outside the set can be added too. A box of n + 1 cells has exactly one solid partition of n inside it, obtained by removing its top cell. A lower set that is not a box has two cells with nothing of the set strictly above them, the cell of largest coordinate sum and, above any cell not below that one, the cell of largest coordinate sum; removing either leaves a solid partition of n.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("meeussen-2004-solid-partition-first-column-tau4"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("solidcolumn-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Cells() => new Formula.Power(Naturals(), D(4));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula SubsetOf(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.SubsetOf, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Count(Formula variable, Formula condition) =>
        new Formula.Absolute(Seq(OpenBrace, variable, Sp, Mid, Sp, condition, CloseBrace));

    private static Formula SolidFormula()
    {
        Formula n = F.Id("n"), cells = F.Id("I"), a = F.Id("a"), b = F.Id("b");
        Formula lower = All("a", cells, All("b", Cells(), Implies(AtMost(b, a), Member(b, cells))));
        return Disp(Iff(Call("IsSolidPartition", n, cells),
            And(Parenthesized(lower), Equal(new Formula.Absolute(cells), n))));
    }

    private static Formula ExtensionsFormula()
    {
        Formula n = F.Id("n"), small = F.Id("I"), large = F.Id("J");
        return Disp(Equal(Call("extensions", n, small),
            Count(large, And(Call("IsSolidPartition", Add(n, D(1)), large), SubsetOf(small, large)))));
    }

    private static Formula ShrinkingsFormula()
    {
        Formula n = F.Id("n"), small = F.Id("I"), large = F.Id("J");
        return Disp(Equal(Call("shrinkings", n, large),
            Count(small, And(Call("IsSolidPartition", n, small), SubsetOf(small, large)))));
    }

    private static Formula ColumnFormula()
    {
        Formula n = F.Id("n"), small = F.Id("I");
        return Disp(Equal(Call("a098052FirstColumn", n),
            Count(small, And(Call("IsSolidPartition", n, small), Equal(Call("extensions", n, small), D(4))))));
    }

    private static Formula ShrinkColumnFormula()
    {
        Formula n = F.Id("n"), large = F.Id("J");
        return Disp(Equal(Call("a098530FirstColumn", n),
            Count(large, And(Call("IsSolidPartition", Add(n, D(1)), large),
                Equal(Call("shrinkings", n, large), D(1))))));
    }

    private static Formula TauFormula()
    {
        Formula n = F.Id("n"), v = F.Id("v");
        Formula product = Seq(Prod, Underscore, Grp(F.Id("i")), Sp, new Formula.Subscript(v, F.Id("i")));
        return Disp(Equal(Call("tau4", n), Count(Member(v, Cells()), Equal(product, n))));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n");
        Formula body = All("n", Naturals(), Implies(AtMost(D(1), n),
            And(Equal(Call("a098052FirstColumn", n), Call("tau4", n)),
                Equal(Call("a098530FirstColumn", n), Call("tau4", Add(n, D(1)))))));
        return Disp(Iff(F.Id("claim"), body));
    }
}
