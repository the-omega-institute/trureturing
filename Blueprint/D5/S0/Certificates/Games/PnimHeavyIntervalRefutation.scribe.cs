using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Games;

internal sealed class PnimHeavyIntervalRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/Games/PnimHeavyIntervalRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/gottlieb2025pnim");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The PNim heavy-interval conjecture fails at a = 8, b = 7.",
        H("A nonheavy partition below a heavy rectangle"),
        Blocks(
            Definition("Position", "Row lengths",
                Equal(F.Id("Position"), Call("List", Naturals())),
                "Positions are lists of natural row lengths. The predicate IsPartition "
                    + "restricts them to nonincreasing positive lists, including the empty list."),
            Definition("deleteColumns", "Deleting diagram columns", DeleteColumnsFormula(),
                "Columns are numbered from zero. Each row n loses precisely the deleted "
                    + "indices j smaller than n; rows reduced to zero are omitted. Remaining "
                    + "columns merge. The filter tests are Boolean comparisons. The deleted "
                    + "list is generated without repetition from the first-row column range."),
            Definition("rowMoves", "Deleting nonempty row subsets", RowMovesFormula(),
                "List.sublists enumerates all retained row subsequences. Strictly smaller "
                    + "length selects exactly deletions of at least one row; the empty "
                    + "subsequence deletes every row."),
            Definition("columnMoves", "Deleting nonempty column subsets", ColumnMovesFormula(),
                "The first row supplies every diagram column of a partition. All nonempty "
                    + "subsets of its zero-based range are deleted by deleteColumns. headD(p,0) "
                    + "is the first row, with default zero for the empty list."),
            Definition("moves", "All PNim followers", MovesFormula(),
                "The row and column options are concatenated, then restricted to strictly "
                    + "smaller cell count. This last filter changes no move of a positive "
                    + "nonincreasing partition. It extends termination to arbitrary natural "
                    + "lists. Repeated followers do not affect the finite set used by mex."),
            Definition("mex", "The least excluded natural number", MexFormula(),
                "mex(s) is the least natural number absent from s, computed as the "
                    + "minimum of the finite set range(card(s)+1) minus s; that set is "
                    + "nonempty because s cannot contain all of the card(s)+1 numbers below "
                    + "card(s)+1."),
            Definition("grundy", "Grundy evaluation by cell count", GrundyFormula(),
                "The Lean definition uses well-founded recursion on cell count; the "
                    + "termination measure and the nonemptiness of the finite set behind "
                    + "each minimum are discharged inside the definition and are not part "
                    + "of the mathematical statement. The terminal empty list has value zero."),
            Definition("IsPartition", "Positive nonincreasing partitions", PartitionFormula(),
                "Pairwise requires each earlier row to be at least each later row. "
                    + "The Boolean all test requires every row length to be positive."),
            Definition("youngLE", "Young's-lattice order", YoungFormula(),
                "The lower list must be no longer than the upper list, and each aligned "
                    + "pair must satisfy first component at most second component. zip "
                    + "therefore checks every lower row. fst and snd denote pair projections."),
            Definition("rectangle", "The upper rectangle", RectangleFormula(),
                "The rectangle contains b+1 copies of a+1, exactly the upper endpoint "
                    + "in printed Conjecture 2."),
            Definition("staircase", "The lower staircase", StaircaseFormula(),
                "Mapping i to a+1-i over range(b+1) gives [a+1,a,...,a-b+1]. "
                    + "Subtraction is natural subtraction; b at most a makes all parts positive."),
            Definition("heavy", "Heaviness and longest play", HeavyFormula(),
                "A nonempty partition is heavy when its Grundy value equals its first "
                    + "row plus its row count minus one. Proposition 2 gives exactly this "
                    + "longest-play length. All arithmetic here is on natural numbers."),
            Definition("claim", "Conjecture 2 as printed", ClaimFormula(),
                "Natural a,b with b at most a encode exactly the integer parameters for "
                    + "which both endpoints are partitions. For every partition p in the "
                    + "closed Young interval, the conjecture predicts heaviness whenever "
                    + "the upper rectangle is heavy."),
            Describe.Lean(DescribeId.Create("pnim-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The printed heavy-interval conjecture is false"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "At a=8 and b=7 the rectangle is [9,9,9,9,9,9,9,9], with Grundy "
                        + "value 16 and longest-play length 16. The partition "
                        + "[9,9,8,8,8,5,5,5] lies above [9,8,7,6,5,4,3,2] and below "
                        + "that rectangle, but its Grundy value is 3 rather than 16.")),
                    Paragraph(Text(
                    "A finite table contains the partition and all its descendants. "
                        + "At every entry, the kernel verifies that all followers are "
                        + "present, the assigned value is absent from their values, and "
                        + "every smaller natural occurs. Induction on cell count equates "
                        + "the table with the recursive Grundy function. A second table "
                        + "establishes the rectangle premise. Only printed Conjecture 2 "
                        + "is refuted; no priority or corrected formula is asserted."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "gottlieb-krnc-mursic-pnim-heavy-interval-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Definition(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("pnim-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula DeleteColumnsFormula()
    {
        var p = F.Id("p");
        var deleted = F.Id("deleted");
        var n = F.Id("n");
        var j = F.Id("j");
        var removed = QualifiedCall("List", "length",
            QualifiedCall("List", "filter", Lam(j, Less(j, n)), deleted));
        return Bound("p", F.Id("Position"), Bound("deleted", F.Id("Position"),
            Equal(Call("deleteColumns", p, deleted), QualifiedCall("List", "filter",
                Lam(n, NotEqual(n, D(0))),
                QualifiedCall("List", "map", Lam(n, Subtract(n, removed)), p)))));
    }

    private static Formula RowMovesFormula()
    {
        var p = F.Id("p");
        var q = F.Id("q");
        return Bound("p", F.Id("Position"), Equal(Call("rowMoves", p),
            QualifiedCall("List", "filter", Lam(q, Less(Call("length", q), Call("length", p))),
                QualifiedCall("List", "sublists", p))));
    }

    private static Formula ColumnMovesFormula()
    {
        var p = F.Id("p");
        var deleted = F.Id("deleted");
        var subsets = QualifiedCall("List", "sublists",
            QualifiedCall("List", "range", Call("headD", p, D(0))));
        return Bound("p", F.Id("Position"), Equal(Call("columnMoves", p),
            QualifiedCall("List", "map", Lam(deleted, Call("deleteColumns", p, deleted)),
                QualifiedCall("List", "filter", Lam(deleted, NotEqual(deleted, EmptyList())), subsets))));
    }

    private static Formula MovesFormula()
    {
        var p = F.Id("p");
        var q = F.Id("q");
        return Bound("p", F.Id("Position"), Equal(Call("moves", p),
            QualifiedCall("List", "filter", Lam(q, Less(Call("sum", q), Call("sum", p))),
                QualifiedCall("List", "append", Call("rowMoves", p), Call("columnMoves", p)))));
    }

    private static Formula MexFormula()
    {
        var s = F.Id("s");
        var candidates = QualifiedCall("Finset", "range", Add(Call("card", s), D(1)));
        return Bound("s", Call("Finset", Naturals()),
            Equal(Call("mex", s), Call("min", Seq(candidates, Sp, Setminus, Sp, s))));
    }

    private static Formula GrundyFormula()
    {
        var p = F.Id("p");
        var q = F.Id("q");
        var values = new Formula.SetBuilder(Call("grundy", q), q, Call("moves", p));
        return Bound("p", F.Id("Position"),
            Equal(Call("grundy", p), Call("mex", values)));
    }

    private static Formula PartitionFormula()
    {
        var p = F.Id("p");
        var x = F.Id("x");
        var y = F.Id("y");
        var n = F.Id("n");
        return Bound("p", F.Id("Position"), Iff(Call("IsPartition", p),
            And(QualifiedCall("List", "Pairwise", Lam(x, Lam(y, GreaterEqual(x, y))), p),
                Equal(QualifiedCall("List", "all", Lam(n, Greater(n, D(0))), p), F.Id("true")))));
    }

    private static Formula YoungFormula()
    {
        var p = F.Id("p");
        var q = F.Id("q");
        var pair = F.Id("pair");
        return Bound("p", F.Id("Position"), Bound("q", F.Id("Position"),
            Iff(Call("youngLE", p, q), And(LessEqual(Call("length", p), Call("length", q)),
                Equal(QualifiedCall("List", "all",
                    Lam(pair, LessEqual(Call("fst", pair), Call("snd", pair))),
                    QualifiedCall("List", "zip", p, q)), F.Id("true"))))));
    }

    private static Formula RectangleFormula()
    {
        var a = F.Id("a");
        var b = F.Id("b");
        return Bound("a", Naturals(), Bound("b", Naturals(),
            Equal(Call("rectangle", a, b), QualifiedCall("List", "replicate", Add(b, D(1)), Add(a, D(1))))));
    }

    private static Formula StaircaseFormula()
    {
        var a = F.Id("a");
        var b = F.Id("b");
        var i = F.Id("i");
        return Bound("a", Naturals(), Bound("b", Naturals(), Equal(Call("staircase", a, b),
            QualifiedCall("List", "map", Lam(i, Subtract(Add(a, D(1)), i)),
                QualifiedCall("List", "range", Add(b, D(1)))))));
    }

    private static Formula HeavyFormula()
    {
        var p = F.Id("p");
        return Bound("p", F.Id("Position"), Iff(Call("heavy", p),
            And(NotEqual(p, EmptyList()), Equal(Call("grundy", p),
                Subtract(Add(Call("headD", p, D(0)), Call("length", p)), D(1))))));
    }

    private static Formula ClaimFormula()
    {
        var a = F.Id("a");
        var b = F.Id("b");
        var p = F.Id("p");
        var interval = Implies(Call("youngLE", Call("staircase", a, b), p),
            Implies(Call("youngLE", p, Call("rectangle", a, b)), Call("heavy", p)));
        var partitions = Bound("p", F.Id("Position"), Implies(Call("IsPartition", p), interval));
        var parameters = Bound("a", Naturals(), Bound("b", Naturals(),
            Implies(LessEqual(b, a), Implies(Call("heavy", Call("rectangle", a, b)), partitions))));
        return Iff(F.Id("claim"), parameters);
    }

    private static Formula Naturals() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula EmptyList() => Seq(OpenBracket, CloseBracket);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Lam(Formula variable, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, variable, Sp, Mapsto, Sp, body));
    private static Formula Bound(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula QualifiedCall(string owner, string name, params Formula[] arguments) =>
        Apply(Seq(F.Id(owner), Dot, F.Id(name)), arguments);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Greater(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.GreaterThan, right);
    private static Formula GreaterEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.GreaterThanOrEqual, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
