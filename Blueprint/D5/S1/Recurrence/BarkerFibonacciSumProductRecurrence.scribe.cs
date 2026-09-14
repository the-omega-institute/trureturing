using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class BarkerFibonacciSumProductRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/BarkerFibonacciSumProductRecurrence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/barker2014a226857");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Fibonacci sum-product sequence satisfies Barker's three-and-six-step recurrence.",
        H("Barker's Fibonacci Sum-Product Recurrence"),
        Blocks(
            Paragraph(Text(
                "All indices and values are natural numbers. The predicate mem selects "
                    + "numbers that are both a sum of two Fibonacci values and a product "
                    + "of two Fibonacci values. The sequence a uses Nat.nth, whose index is "
                    + "zero-based; the OEIS sequence is one-based, so its definition uses "
                    + "natural subtraction at n = 0.")),
            Node(
                "mem",
                "The Fibonacci sum-product membership predicate",
                MemFormula(),
                "A natural number belongs to mem exactly when it has both a representation "
                    + "as a sum of two Fibonacci numbers and a representation as a product "
                    + "of two Fibonacci numbers. Equal summands or factors are allowed; "
                    + "Fibonacci indexing uses F_0 = 0.",
                DescribeRole.Definition),
            Node(
                "a",
                "The one-based sequence from the membership predicate",
                AFormula(),
                "The Lean sequence is Nat.nth mem (n - 1). Nat.nth enumerates members from "
                    + "zero, while the OEIS offset is one; natural subtraction therefore "
                    + "also specifies the value at n = 0.",
                DescribeRole.Definition),
            Node(
                "barker_a226857",
                "Barker's recurrence",
                RecurrenceFormula(),
                "The classification of the membership set as {F_k, 2F_k, 3F_k}, proved "
                    + "using the product gap invariant and the interleaving of these three "
                    + "families, identifies the explicit enumeration with Nat.nth and yields "
                    + "the recurrence for every n greater than 12. The generating-function "
                    + "line and the accompanying %C corollaries are not claimed.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a226857-fibonacci-sum-product-recurrence"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(
        string name,
        string title,
        Formula formula,
        string prose,
        DescribeRole role,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a226857-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name),
        H(title),
        StatementSource.FromAuthor(formula),
        role is DescribeRole.Definition
            ? AssessedProvenance.FromLiterature(Source)
            : AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))),
        role,
        claim);

    private static Formula MemFormula() => Disp(ForAll(
        new[] { Bound("x") },
        Iff(
            Call("mem", X()),
            Parenthesized(And(
                Exists(new[] { Bound("i"), Bound("j") },
                    Equal(X(), Add(Fib(I()), Fib(J())))),
                Exists(new[] { Bound("r"), Bound("s") },
                    Equal(X(), Mul(Fib(R()), Fib(S())))))))));

    private static Formula AFormula() => Disp(ForAll(
        new[] { Bound("n") },
        Equal(Call("a", N()),
            Call("nth", F.Id("mem"), Subtract(N(), D(1))))));

    private static Formula RecurrenceFormula() => Disp(ForAll(
        new[] { Bound("n") },
        Implies(
            Less(D(1, 2), N()),
            Equal(
                Call("a", N()),
                Add(
                    Call("a", Subtract(N(), D(3))),
                    Call("a", Subtract(N(), D(6))))))));

    private static Formula X() => F.Id("x");
    private static Formula I() => F.Id("i");
    private static Formula J() => F.Id("j");
    private static Formula R() => F.Id("r");
    private static Formula S() => F.Id("s");
    private static Formula N() => F.Id("n");

    private static Formula.BoundVariable Bound(string name) =>
        new Formula.BoundVariable(FormulaIdentifier.Create(name), Naturals());

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Exists(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Equal(Formula left, Formula right) =>
        Seq(left, Sp, Eq, Sp, right);

    private static Formula Less(Formula left, Formula right) =>
        Seq(left, Sp, Lt, Sp, right);

    private static Formula Add(Formula left, Formula right) =>
        Seq(left, Sp, Plus, Sp, right);

    private static Formula Subtract(Formula left, Formula right) =>
        Seq(left, Sp, Minus, Sp, right);

    private static Formula Mul(Formula left, Formula right) =>
        Seq(left, Sp, Times, Sp, right);

    private static Formula Fib(Formula index) => Call("fib", index);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
