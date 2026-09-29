using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class LatinEulerianShiftCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/LatinEulerianShiftCount.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/mirzavaziri2026latin");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Swapping the two least residues changes only the two endpoint comparisons in a cyclic shift.",
        H("Residue Comparisons After Swapping Zero and One"),
        Blocks(
            Node("swap-zero-one", "Residue transposition", "swap01", SwapFormula(),
                "The map exchanges zero and one and fixes every other natural residue.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("shifted-comparison", "Shifted comparison characterization", "shifted_comparison",
                ComparisonFormula(),
                "For a nonzero shift smaller than the modulus, the swapped comparison holds on the ordinary nonwrapping interval, except for the zero to one step, together with the one to zero endpoint when the shift is the predecessor residue.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("shifted-ascents", "Shifted ascent count", "shiftedAscents", AscentsFormula(),
                "Count the residues whose shifted pair is increasing after the transposition.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("shifted-ascent-count", "Shifted ascent formula", "shifted_ascent_count",
                CountFormula(),
                "The count is n minus d, with one correction when d is one and one correction when d is n minus one.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role,
        AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula And(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Or(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.Or, result);
        return result;
    }
    private static Formula Not(Formula value) =>
        new Formula.Not(value);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula SwapFormula()
    {
        var x = F.Id("x");
        return Disp(All("x", Nat(), Eq(Call("swap01", x),
            Call("if", Eq(x, D(0)), D(1), Call("if", Eq(x, D(1)), D(0), x)))));
    }

    private static Formula ComparisonFormula()
    {
        var n = F.Id("n"); var d = F.Id("d"); var x = F.Id("x");
        var left = Lt(Call("swap01", x), Call("swap01", Call("mod", Add(x, d), n)));
        var right = Or(And(Lt(x, Sub(n, d)), Not(And(Eq(d, D(1)), Eq(x, D(0))))),
            And(Eq(d, Sub(n, D(1))), Eq(x, D(1))));
        var hypotheses = And(Le(D(3), n), And(Lt(D(0), d), And(Lt(d, n), Lt(x, n))));
        return Disp(All("n", Nat(), All("d", Nat(), All("x", Nat(),
            new Formula.Logic(hypotheses, FormulaLogicOperator.Implies,
                Iff(left, right))))));
    }

    private static Formula AscentsFormula()
    {
        var n = F.Id("n"); var d = F.Id("d"); var x = F.Id("x");
        var set = Seq(OpenBrace, x, Sp, InMacro, Sp, Nat(), Bar, Sp,
            And(Lt(x, n), Lt(Call("swap01", x),
                Call("swap01", Call("mod", Add(x, d), n)))), CloseBrace);
        return Disp(All("n", Nat(), All("d", Nat(),
            Eq(Call("shiftedAscents", n, d), Call("card", set)))));
    }

    private static Formula CountFormula()
    {
        var n = F.Id("n"); var d = F.Id("d");
        var hypotheses = And(Le(D(3), n), And(Lt(D(0), d), Lt(d, n)));
        var left = Add(Call("shiftedAscents", n, d), Call("if", Eq(d, D(1)), D(1), D(0)));
        var right = Add(Sub(n, d), Call("if", Eq(d, Sub(n, D(1))), D(1), D(0)));
        return Disp(All("n", Nat(), All("d", Nat(),
            new Formula.Logic(hypotheses, FormulaLogicOperator.Implies, Eq(left, right)))));
    }
}
