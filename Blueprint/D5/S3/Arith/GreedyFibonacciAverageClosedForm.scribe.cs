using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class GreedyFibonacciAverageClosedFormDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/GreedyFibonacciAverageClosedForm.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/fried2025proofs");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The greedy sequence whose running averages are Fibonacci takes the conjectured closed "
            + "form from the tenth term onwards.",
        H("A Closed Form for the Greedy Fibonacci-Average Sequence"),
        Blocks(
            Node("fibonacci-membership", "Being a Fibonacci number", "IsFib",
                IsFibFormula(),
                "The source speaks of a number being a Fibonacci number; that is the property "
                    + "displayed here. It is decidable, because an index whose Fibonacci value "
                    + "is a given number is at most that number plus one.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("admissible-value", "An admissible next value", "Good",
                GoodFormula(),
                "The source builds its sequence from distinct least positive numbers whose "
                    + "running averages are Fibonacci numbers. After the first terms have been "
                    + "written down, a candidate is admissible exactly when it is positive, has "
                    + "not been used, and makes the average of the terms written so far together "
                    + "with it a Fibonacci number. The average is expressed as divisibility of "
                    + "the new total by the number of terms together with the quotient being a "
                    + "Fibonacci number.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("admissible-value-exists", "Some value is always admissible", "good_exists",
                GoodExistsFormula(),
                "Taking the index twice the current total plus two gives a Fibonacci number "
                    + "larger than that total, so the difference is positive, exceeds every term "
                    + "already written, and leaves the required quotient. The greedy rule "
                    + "therefore never stalls and the sequence is defined at every index.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("greedy-value", "The greedy value", "nextVal",
                NextValFormula(),
                "The least admissible value, which exists by the previous statement. The word "
                    + "least is the one the source uses.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("history", "The terms written so far", "hist",
                HistFormula(),
                "The list of the first terms, extended one term at a time by the greedy value "
                    + "for the next index.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("sequence", "The sequence itself", "a",
                SequenceFormula(),
                "The source writes this sequence with subscripts from one. Its entry at an index "
                    + "is the greedy value taken after the preceding terms.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("even-index-value", "The value at an even index", "X",
                XFormula(),
                "The source displays the even case of its closed form as the index times the "
                    + "Fibonacci number three beyond half the index, less one below the index "
                    + "times the Fibonacci number two beyond half the index. Expanding the "
                    + "Fibonacci recurrence once turns that into the expression displayed here, "
                    + "which involves no subtraction.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("first-ten", "The first ten terms", "base10",
                BaseFormula(),
                "The terms the greedy rule produces before the closed form takes over. The "
                    + "source states its closed form from the tenth term onwards, and these are "
                    + "the values below that point together with the tenth.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("later-terms", "The terms from the eleventh onwards", "tailList",
                TailFormula(),
                "From the eleventh term the values come in pairs: a Fibonacci number at an odd "
                    + "index, then the even-index value at the next one.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("closed-form-statement", "The conjectured closed form", "claim",
                ClaimFormula(),
                "Section 6 of the source reads verbatim: \"Refining the conjecture stated in "
                    + "A248982 regarding a closed-form formula, it seems that, for n at least "
                    + "ten, we have a n equals n times F of n over two plus three minus n minus "
                    + "one times F of n over two plus two if n is even, and F of n plus one over "
                    + "two plus two otherwise.\" The even case is displayed here additively so "
                    + "that no truncated subtraction occurs. The sequence entry carries two "
                    + "further standing conjectures, an order eight linear recurrence beyond the "
                    + "seventeenth term and the identification of the odd-index terms with "
                    + "Fibonacci numbers; both follow from the displayed form.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("closed-form-proved", "The closed form holds", "result",
                ResultFormula(),
                "Write S for the total of the terms written so far. The argument is a two step "
                    + "induction on the claim that after an even index twice j the total is "
                    + "twice j times the Fibonacci number three beyond j, and after the next "
                    + "index it is one more than twice j times that same Fibonacci number. The "
                    + "base is the tenth term, where the total is two hundred ten. At an odd "
                    + "index the least admissible Fibonacci average is the one three beyond j, "
                    + "because a smaller one would not raise the total; the resulting value is "
                    + "that Fibonacci number itself. At the following even index the same "
                    + "Fibonacci average would repeat the value just used, so the rule moves to "
                    + "the next one and the value is the even-index expression. What separates "
                    + "the two families is that no even-index value is a Fibonacci number, which "
                    + "is the frozen statement this module depends on. The remaining exclusions "
                    + "are inequalities between consecutive Fibonacci numbers, together with the "
                    + "observation that the even-index values increase and that the first nine "
                    + "terms are all below both families from the tenth onwards.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("greedy-fibonacci-average-closed-form"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role,
            resolution);

    private static Formula Fib(Formula argument) => Call("fib", argument);
    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula ListOfNaturals() => Call("List", Naturals());
    private static Formula EmptyList() => Seq(OpenBracket, CloseBracket);
    private static Formula OneList(Formula x) => Seq(OpenBracket, x, CloseBracket);
    private static Formula TwoList(Formula x, Formula y) =>
        Seq(OpenBracket, x, Comma, Sp, y, CloseBracket);

    private static Formula IsFibFormula()
    {
        var k = F.Id("k");
        var m = F.Id("m");
        return Disp(Universal("k", Naturals(),
            Iff(Call("IsFib", k), Exists("m", Naturals(), Equal(Fib(m), k)))));
    }

    private static Formula GoodFormula()
    {
        var l = F.Id("L");
        var n = F.Id("n");
        var v = F.Id("v");
        var total = Add(Call("sum", l), v);
        var body = And(Less(D(0), v),
            And(new Formula.Not(Parenthesized(Member(v, l))),
                And(Divides(n, total), Call("IsFib", Call("div", total, n)))));
        return Disp(Universal("L", ListOfNaturals(),
            Universal("n", Naturals(),
                Universal("v", Naturals(), Iff(Call("Good", l, n, v), body)))));
    }

    private static Formula GoodExistsFormula()
    {
        var l = F.Id("L");
        var n = F.Id("n");
        var v = F.Id("v");
        return Disp(Universal("L", ListOfNaturals(),
            Universal("n", Naturals(),
                Implies(Less(D(0), n), Exists("v", Naturals(), Call("Good", l, n, v))))));
    }

    private static Formula NextValFormula()
    {
        var l = F.Id("L");
        var n = F.Id("n");
        var v = F.Id("v");
        var set = SetBuilder(Typed(v, Naturals()), Call("Good", l, n, v));
        return Disp(Universal("L", ListOfNaturals(),
            Universal("n", Naturals(),
                Implies(Less(D(0), n), Equal(Call("nextVal", l, n), Call("min", set))))));
    }

    private static Formula HistFormula()
    {
        var n = F.Id("n");
        var basis = Equal(Call("hist", D(0)), EmptyList());
        var recursion = Equal(Call("hist", Add(n, D(1))),
            Call("append", Call("hist", n),
                OneList(Call("nextVal", Call("hist", n), Add(n, D(1))))));
        return Disp(Universal("n", Naturals(), Seq(basis, Sp, Sp, Sp, recursion)));
    }

    private static Formula SequenceFormula()
    {
        var n = F.Id("n");
        return Disp(Universal("n", Naturals(),
            Equal(Call("a", n), Call("nextVal", Call("hist", Subtract(n, D(1))), n))));
    }

    private static Formula XFormula()
    {
        var j = F.Id("j");
        return Disp(Universal("j", Naturals(),
            Equal(Call("X", j),
                Add(Fib(Add(j, D(2))),
                    Multiply(Multiply(D(2), j), Fib(Add(j, D(1))))))));
    }

    private static Formula BaseFormula() =>
        Disp(Equal(F.Id("base10"),
            Seq(OpenBracket, D(1), Comma, Sp, D(3), Comma, Sp, D(2), Comma, Sp, D(6), Comma, Sp,
                D(1, 3), Comma, Sp, D(5), Comma, Sp, D(2, 6), Comma, Sp, D(8), Comma, Sp,
                D(5, 3), Comma, Sp, D(9, 3), CloseBracket)));

    private static Formula TailFormula()
    {
        var k = F.Id("k");
        var basis = Equal(Call("tailList", D(0)), EmptyList());
        var recursion = Equal(Call("tailList", Add(k, D(1))),
            Call("append", Call("tailList", k),
                TwoList(Fib(Add(k, D(8))), Call("X", Add(k, D(6))))));
        return Disp(Universal("k", Naturals(), Seq(basis, Sp, Sp, Sp, recursion)));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n");
        var half = Call("div", n, D(2));
        var evenCase = Implies(Equal(Call("mod", n, D(2)), D(0)),
            Equal(Add(Call("a", n), Multiply(Subtract(n, D(1)), Fib(Add(half, D(2))))),
                Multiply(n, Fib(Add(half, D(3))))));
        var oddCase = Implies(Equal(Call("mod", n, D(2)), D(1)),
            Equal(Call("a", n),
                Fib(Add(Call("div", Add(n, D(1)), D(2)), D(2)))));
        var body = Universal("n", Naturals(),
            Implies(LessEqual(D(1, 0), n), And(evenCase, oddCase)));
        return Disp(Iff(F.Id("claim"), body));
    }

    private static Formula ResultFormula() => Disp(F.Id("claim"));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula SetBuilder(Formula binder, Formula predicate) =>
        Seq(OpenBrace, binder, Sp, Mid, Sp, predicate, CloseBrace);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Member(Formula element, Formula collection) =>
        new Formula.Relation(element, FormulaRelationOperator.MemberOf, collection);

    private static Formula Divides(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Divides, right);

    private static Formula Universal(string name, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
}
