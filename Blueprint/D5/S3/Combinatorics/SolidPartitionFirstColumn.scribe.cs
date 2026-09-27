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
        "In every dimension d, the d-dimensional partitions of n that extend in exactly d ways to a partition of n + 1, and the d-dimensional partitions of n + 1 that contain exactly one partition of n, are the boxes, so both are counted by the number of ordered factorizations of n, respectively n + 1, into d factors; for d = 4 these are the first columns of A098052 and A098530 on solid partitions.",
        H("Partitions with the fewest extensions are boxes"),
        Blocks(
            Node("solid", "Partitions in dimension d", SolidFormula(),
                "A d-dimensional partition of n is read through its Ferrers diagram: a finite set of n cells of the d-th power of the natural numbers that contains every cell below any of its cells in the coordinatewise order. For d = 4 these are the solid partitions of A000293.",
                "IsSolidPartition", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("extensions", "Extensions", ExtensionsFormula(),
                "The number of d-dimensional partitions of n + 1 that contain I (A098052 counts the solid partitions of n by this number).",
                "extensions", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("shrinkings", "Shrinkings", ShrinkingsFormula(),
                "The number of d-dimensional partitions of n contained in J (A098530 counts the solid partitions of n + 1 by this number).",
                "shrinkings", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("column", "Partitions with d extensions", ColumnFormula(),
                "The number of d-dimensional partitions of n that extend in exactly d ways; for d = 4 the first column of A098052.",
                "firstColumn", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("shrinkcolumn", "Partitions with one shrinking", ShrinkColumnFormula(),
                "The number of d-dimensional partitions of n + 1 that shrink in exactly one way; for d = 4 the first column of A098530.",
                "shrinkColumn", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("tau", "Ordered factorizations into d factors", TauFormula(),
                "The Piltz function: the number of ordered d-tuples of natural numbers whose product is n (A007426 for d = 4).",
                "tau", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The first-column conjectures in every dimension", ClaimFormula(),
                "For every d at least 1 and n at least 1, the partitions of n with exactly d extensions number tau_d(n), and the partitions of n + 1 with exactly one shrinking number tau_d(n + 1); for d = 4 these are the first-column conjectures of A098052 and A098530.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Proof of the conjectures", Disp(F.Id("claim")),
                "For positive v the box of cells c with c_i < v_i for every i is a lower set with the product of the v_i cells, and it determines v; so boxes of n cells correspond to ordered factorizations of n into d factors. The partitions of n + 1 containing a box are exactly the box with one of the d axis cells v_i e_i added: every cell strictly below the new cell lies in the box, which forces the new cell onto an axis at distance v_i. A nonempty lower set that is not a box has a further extension: with v_i one more than its largest i-th coordinate the d axis cells can be added, and a minimal cell of the box of v outside the set can be added too. A box of n + 1 cells has exactly one partition of n inside it, obtained by removing its top cell. A lower set that is not a box has two cells with nothing of the set strictly above them, a maximal cell and a maximal cell above any cell not below that one; removing either leaves a partition of n.",
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
    private static Formula Cells() => new Formula.Power(Naturals(), F.Id("d"));
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
        Formula d = F.Id("d"), n = F.Id("n"), small = F.Id("I");
        return Disp(Equal(Call("firstColumn", d, n),
            Count(small, And(Call("IsSolidPartition", n, small), Equal(Call("extensions", n, small), d)))));
    }

    private static Formula ShrinkColumnFormula()
    {
        Formula d = F.Id("d"), n = F.Id("n"), large = F.Id("J");
        return Disp(Equal(Call("shrinkColumn", d, n),
            Count(large, And(Call("IsSolidPartition", Add(n, D(1)), large),
                Equal(Call("shrinkings", n, large), D(1))))));
    }

    private static Formula TauFormula()
    {
        Formula d = F.Id("d"), n = F.Id("n"), v = F.Id("v");
        Formula product = Seq(Prod, Underscore, Grp(F.Id("i")), Sp, new Formula.Subscript(v, F.Id("i")));
        return Disp(Equal(Call("tau", d, n), Count(Member(v, Cells()), Equal(product, n))));
    }

    private static Formula ClaimFormula()
    {
        Formula d = F.Id("d"), n = F.Id("n");
        Formula body = All("d", Naturals(), All("n", Naturals(), Implies(And(AtMost(D(1), d), AtMost(D(1), n)),
            And(Equal(Call("firstColumn", d, n), Call("tau", d, n)),
                Equal(Call("shrinkColumn", d, n), Call("tau", d, Add(n, D(1))))))));
        return Disp(Iff(F.Id("claim"), body));
    }
}
