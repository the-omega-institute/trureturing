using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class VosPostLogBoundedSemiprimePartitionRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Congruence/VosPostLogBoundedSemiprimePartitionRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/vospost2004a100952");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A residue-class obstruction refutes the log-bounded partition conjecture in A100952.",
        H("The OEIS A100952 Log-Bounded Semiprime-Partition Conjecture"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a100952-log-bounded-representation"),
                DeclarationHandle.Create(Prefix + "Rep"),
                H("A log-bounded prime-plus-semiprime representation"),
                StatementSource.FromAuthor(RepFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The three variables p, q, and r are natural primes. The inequality "
                        + "casts p and min(q,r) to real numbers and uses Real.log, the "
                        + "natural logarithm. Equal semiprime factors q and r are allowed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a100952-eventual-log-bounded-partition"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The eventual log-bounded partition conjecture"),
                StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "This is the source's allowance for a threshold larger than sixty: "
                        + "some natural B at least sixty works for every natural m above B."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a100952-eventual-log-bounded-partition-refuted"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The eventual conjecture is false"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Every number 6t+5 fails. The logarithmic estimate first forces q and r "
                        + "above three; parity then forces p=2; divisibility by three finally "
                        + "forces q=3 or r=3, a contradiction. The completeness conjecture "
                        + "for A100952 is untouched."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a100952-log-bounded-semiprime-partition-refutation"),
                    ResolutionKind.Refuted)))));

    private static Formula RepFormula()
    {
        var m = F.Id("m");
        var p = F.Id("p");
        var q = F.Id("q");
        var r = F.Id("r");
        var representation = Exists(
            [Bound("p"), Bound("q"), Bound("r")],
            And(
                Prime(p),
                And(
                    Prime(q),
                    And(
                        Prime(r),
                        And(
                            Equal(m, Add(p, Multiply(q, r))),
                            AtMost(Coerce(p, Reals()),
                                Call("log", Coerce(Call("min", q, r), Reals()))))))));
        return Disp(ForAll([Bound("m")],
            Iff(Call("Rep", m), Parenthesized(representation))));
    }

    private static Formula ClaimFormula()
    {
        var cutoff = F.Id("B");
        var m = F.Id("m");
        var tail = ForAll([Bound("m")],
            Implies(Less(cutoff, m), Call("Rep", m)));
        var body = Exists([Bound("B")],
            And(AtMost(Num(60), cutoff), tail));
        return Disp(Iff(F.Id("claim"), Parenthesized(body)));
    }

    private static Formula ResultFormula() =>
        Disp(new Formula.Not(F.Id("claim")));

    private static Formula.BoundVariable Bound(string name) => new(
        FormulaIdentifier.Create(name), Naturals());

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Exists(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Reals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Real"));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Prime(Formula value) => Call("Prime", value);

    private static Formula Coerce(Formula value, Formula type) =>
        Parenthesized(Seq(value, Sp, Colon, Sp, type));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And,
            Parenthesized(right));

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff,
            Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies,
            Parenthesized(right));
}
