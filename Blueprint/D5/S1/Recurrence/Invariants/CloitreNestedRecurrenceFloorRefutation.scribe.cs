using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class CloitreNestedRecurrenceFloorRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Invariants/CloitreNestedRecurrenceFloorRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/cloitre2002a076502");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cloitre's floor-offset conjecture for A076502 fails at n = 1167.",
        H("The OEIS A076502 Nested-Recurrence Floor-Offset Conjecture"),
        Blocks(
            Node("a", "The nested recurrence", SequenceFormula(),
                "The value a(0)=0 is a sentinel outside Cloitre's offset-one sequence. "
                    + "The two minima keep each recursive index at most n+1. The literal "
                    + "recurrence below shows that both minima select their first arguments.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a_succ", "The literal Cloitre recurrence", RecurrenceFormula(),
                "For n at least two, the bounds 1 <= a(k) <= k make the two clamped "
                    + "indices strictly smaller than n. Thus the total sequence obeys the "
                    + "nested recurrence printed for A076502.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("cubic_positiveRoot_existsUnique", "The positive cubic root",
                CubicRootFormula(),
                "The polynomial is negative at zero and positive at one. It is strictly "
                    + "increasing because, for x<y, twice its divided difference is "
                    + "x^2+y^2+(x+y-1)^2+3, which is positive.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("c", "Cloitre's cubic constant", ConstantFormula(),
                "This is the unique positive real root of x^3-x^2+2x-1, numerically "
                    + "0.5698….",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The bounded-error and floor-offset conjecture", ClaimFormula(),
                "The assertion combines bounded real error with the requirement that every "
                    + "integer difference a(n)-floor(cn) belongs to {0,1,2}.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The floor-offset conjecture fails", ResultFormula(),
                "At n=1167, the recurrence gives a(1167)=664, while the cubic-root "
                    + "isolation gives floor(1167c)=665. Their difference is -1, outside "
                    + "{0,1,2}, so the second conjunct and hence the conjunction are false.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a076502-nested-recurrence-floor-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("a076502-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula SequenceFormula()
    {
        var n = F.Id("n");
        var successor = Add(n, D(1));
        var current = Add(n, D(2));
        var secondIndex = Minimum(Subtract(current, Call("a", successor)), successor);
        var thirdIndex = Minimum(Subtract(current, Call("a", secondIndex)), successor);
        return Disp(new Formula.Aligned([
            Equal(Call("a", D(0)), D(0)),
            Equal(Call("a", D(1)), D(1)),
            ForAll("n", Naturals(),
                Equal(Call("a", current), Subtract(current, Call("a", thirdIndex)))),
        ]));
    }

    private static Formula RecurrenceFormula()
    {
        var n = F.Id("n");
        var predecessor = Subtract(n, D(1));
        var inner = Subtract(n, Call("a", predecessor));
        var middle = Subtract(n, Call("a", inner));
        var outer = Subtract(n, Call("a", middle));
        return Disp(ForAll("n", Naturals(), Implies(
            LessOrEqual(D(2), n),
            Equal(Call("a", n), outer))));
    }

    private static Formula CubicRootFormula()
    {
        var x = F.Id("x");
        var conditions = And(
            Less(D(0), x),
            Equal(Cubic(x), D(0)));
        return Disp(Seq(
            Exists, Bang, Sp, x, Sp, InMacro, Sp, Reals(), Comma, Sp,
            Parenthesized(conditions)));
    }

    private static Formula ConstantFormula()
    {
        var theoremName = Seq(
            Seq(F.Id("cubic"), Underscore, F.Id("p")), F.Id("ositiveRoot"),
            Seq(Underscore, F.Id("e")), F.Id("xistsUnique"));
        return Disp(Equal(
            F.Id("c"),
            Apply(Qualified("Classical", "choose"), theoremName)));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n");
        var realN = Coerce(n, Reals());
        var realA = Coerce(Call("a", n), Reals());
        var scaled = Multiply(F.Id("c"), realN);
        var bound = F.Id("M");
        var boundedError = ExistsIn("M", Reals(),
            ForAll("n", Naturals(), Implies(
                LessOrEqual(D(1), n),
                LessOrEqual(
                    new Formula.Absolute(Subtract(realA, scaled)),
                    bound))));
        var offset = F.Id("j");
        var offsets = new Formula.SetLiteral([D(0), D(1), D(2)]);
        var floorOffset = ForAll("n", Naturals(), Implies(
            LessOrEqual(D(1), n),
            ExistsIn("j", offsets, Equal(
                Coerce(Call("a", n), Integers()),
                Add(Seq(Lfloor, Sp, scaled, Sp, Rfloor), offset)))));
        return Disp(Iff(
            F.Id("claim"),
            Parenthesized(And(
                Parenthesized(boundedError),
                Parenthesized(floorOffset)))));
    }

    private static Formula ResultFormula() =>
        Disp(new Formula.Not(F.Id("claim")));

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Reals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Real"));

    private static Formula Integers() => new Formula.Integers();

    private static Formula ForAll(string variable, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(variable),
            domain,
            body);

    private static Formula ExistsIn(string variable, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create(variable),
            domain,
            body);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Qualified(string prefix, string name) =>
        Seq(F.Id(prefix), Dot, F.Id(name));

    private static Formula Parenthesized(Formula value) =>
        Seq(Open, value, Close);

    private static Formula Coerce(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));

    private static Formula Minimum(Formula left, Formula right) =>
        Call("min", left, right);

    private static Formula Cubic(Formula value) =>
        Subtract(
            Add(
                Subtract(Power(value, D(3)), Power(value, D(2))),
                Multiply(D(2), value)),
            D(1));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);
}
