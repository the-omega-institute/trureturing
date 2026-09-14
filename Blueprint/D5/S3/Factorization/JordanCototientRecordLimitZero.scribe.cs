using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class JordanCototientRecordLimitZeroDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Factorization/JordanCototientRecordLimitZero.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For each positive natural input, eventual strict Jordan-cototient record membership "
            + "at sufficiently small positive parameters is characterized by the number of "
            + "distinct prime factors, with three exceptional values.",
        H("Jordan-Cototient Record Limit at Zero"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a387335-eventual-record-characterization"),
                DeclarationHandle.Create(Prefix + "a387335_eventual_record_iff"),
                H("The eventual record set near zero"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural n >= 1, there is a positive real epsilon such that n "
                            + "is a strict Jordan-cototient record for every real parameter k "
                            + "with 0 < k < epsilon exactly when n is one, two, four, or has at "
                            + "least two distinct prime factors. Equivalently, after the three "
                            + "exceptional values, these eventual records are the non-prime-powers "
                            + "listed by OEIS A024619.")),
                    Paragraph(Text(
                        "The threshold may depend on n. At parameter zero every input n > 1 has "
                            + "Jordan cototient one. Its right derivative is log(n) when n has at "
                            + "least two distinct prime factors, and log(p^(a-1)) when n=p^a. "
                            + "Strict derivative comparisons hold simultaneously for the finitely "
                            + "many positive predecessors of n.")),
                    Paragraph(Text(
                        "For exclusion, an odd prime power p^a with a >= 2 loses to "
                            + "2*p^(a-1), while 2^a with a >= 3 loses to 3*2^(a-2). Every prime "
                            + "greater than two ties with two. These comparisons prove the "
                            + "pointwise eventual characterization stated in the OEIS A387335 "
                            + "comment of Hal M. Switkay dated 2025-11-30."))),
                DescribeRole.Theorem))));

    private static Formula MainFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k"), epsilon = F.Id("epsilon");
        Formula smallPositiveRecord = ExistsMany(
            [Bound("epsilon", Reals())],
            And(
                LessThan(D(0), epsilon),
                ForAllMany(
                    [Bound("k", Reals())],
                    Implies(
                        LessThan(D(0), k),
                        Implies(
                            LessThan(k, epsilon),
                            Call("StrictRecord", k, n))))));
        Formula exceptions = new Formula.Relation(
            n,
            FormulaRelationOperator.MemberOf,
            Seq(OpenBrace, D(1), Comma, Sp, D(2), Comma, Sp, D(4), CloseBrace));
        Formula compositeSupport = LessThanOrEqual(
            D(2), Call("card", Call("primeFactors", n)));
        Formula classification = Or(exceptions, compositeSupport);
        return Disp(ForAllMany(
            [Bound("n", Naturals())],
            Implies(
                LessThanOrEqual(D(1), n),
                Iff(Parenthesized(smallPositiveRecord), Parenthesized(classification)))));
    }

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula.BoundVariable Bound(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);

    private static Formula ForAllMany(
        Formula.BoundVariable[] variables,
        Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula ExistsMany(
        Formula.BoundVariable[] variables,
        Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessThanOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Or, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
}
