using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class StephanSlopingBinaryPeriodRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/StephanSlopingBinaryPeriodRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Digit/cloitre2005a103585");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The 129th and 172nd entries refute the proposed period 43 of OEIS A103585.",
        H("The OEIS A103585 Sloping-Binary Period Conjecture"),
        Blocks(
            Node("a103585-sloping-binary", "The sloping-binary sequence",
                SlopingBinaryFormula(),
                "The value s(k) is A102370(k), written as the finite conditional sum in its "
                    + "OEIS formula.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a103585-selector", "The A103585 selection predicate",
                SelectorFormula(),
                "The predicate P selects exactly those natural k for which s(k) equals k+2.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a103585-sequence", "The zero-based A103585 sequence",
                SequenceFormula(),
                "The value A(i) is the i-th natural satisfying P, reduced modulo four. Thus "
                    + "OEIS a(m) equals A(m-1).",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a103585-period-claim", "Stephan's period-43 claim",
                ClaimFormula(),
                "The claim asserts that shifting any zero-based index by 43 preserves A.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a103585-period-refuted", "The period-43 claim fails",
                ResultFormula(),
                "The finite ranking certificate identifies the 129th entry with 383 modulo "
                    + "four and the 172nd entry with 513 modulo four. Hence a(129)=3 differs "
                    + "from a(172)=1. This refutes the period-43 claim without changing the "
                    + "definition of A102370 or asserting a true period.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a103585-sloping-binary-period-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(
        string id,
        string title,
        Formula formula,
        string prose,
        DescribeRole role,
        AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + DeclarationName(id)),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, claim);

    private static string DeclarationName(string id) => id switch
    {
        "a103585-sloping-binary" => "s",
        "a103585-selector" => "P",
        "a103585-sequence" => "A",
        "a103585-period-claim" => "claim",
        "a103585-period-refuted" => "result",
        _ => throw new ArgumentOutOfRangeException(nameof(id)),
    };

    private static Formula SlopingBinaryFormula()
    {
        var k = F.Id("k");
        var m = F.Id("m");
        var power = new Formula.Power(D(2), m);
        var condition = Equal(new Formula.Modulo(Add(k, m), power), D(0));
        var summand = Call("ite", condition, power, D(0));
        var interval = Call("Icc", D(1), Add(k, D(1)));
        var sum = Seq(
            new Formula.Subscript(F.Sum, Seq(m, Sp, InMacro, Sp, interval)),
            Sp, Parenthesized(summand));
        return Disp(Universal("k", Equal(Call("s", k), Add(k, sum))));
    }

    private static Formula SelectorFormula()
    {
        var k = F.Id("k");
        var definition = new Formula.Logic(
            Parenthesized(Call("P", k)),
            FormulaLogicOperator.Iff,
            Parenthesized(Equal(Call("s", k), Add(k, D(2)))));
        return Disp(Universal("k", definition));
    }

    private static Formula SequenceFormula()
    {
        var i = F.Id("i");
        var nth = Call("nth", F.Id("P"), i);
        return Disp(Universal("i", Equal(Call("A", i), new Formula.Modulo(nth, D(4)))));
    }

    private static Formula ClaimFormula()
    {
        var i = F.Id("i");
        var periodicity = Universal(
            "i", Equal(Call("A", Add(i, D(4, 3))), Call("A", i)));
        return Disp(new Formula.Logic(
            Parenthesized(F.Id("claim")),
            FormulaLogicOperator.Iff,
            Parenthesized(periodicity)));
    }

    private static Formula ResultFormula() =>
        Disp(new Formula.Not(F.Id("claim")));

    private static Formula Universal(string variable, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(variable),
            Naturals(),
            body);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
