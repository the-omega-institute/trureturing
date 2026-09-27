using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class PisanoOrderRangeRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/PisanoOrderRangeRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/benfieldlippard2025pisanozeros");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A two-term recurrence modulo thirteen has three zeros in one period, so the "
            + "conjectured range for the number of such zeros is wrong.",
        H("The Number of Zeros in a Period Is Not Confined to Two"),
        Blocks(
            Node("order-of-a-modulus", "The order of a modulus", "pisanoOrder",
                OrderFormula(),
                "The source calls the number of zeros in one period of the recurrence the order "
                    + "of the modulus. Zeros of the sequence occur exactly at the multiples of "
                    + "the entry point, the least index at which the modulus divides a term, and "
                    + "the entry point divides the period because a period ends on a zero. So "
                    + "the multiples of the entry point below the period are counted by the "
                    + "quotient, and that quotient is the order.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("conjectured-range", "The conjectured range", "claim",
                ClaimFormula(),
                "The source writes the sequence as starting at zero and one and continuing by "
                    + "the rule that each term is the first parameter times the previous term "
                    + "plus the second parameter times the one before that. For the case where "
                    + "the second parameter is neither one nor minus one and the absolute value "
                    + "of the first exceeds the absolute value of the second by one, it asserts "
                    + "that the order takes only the values zero, one and two. Here the "
                    + "parameters are carried in the form this repository uses, where the "
                    + "recurrence subtracts the second parameter, so the pair is the first "
                    + "parameter together with the negative of the second; and the second "
                    + "parameter is required to be invertible, which restricts the assertion to "
                    + "moduli for which the sequence is periodic from the start. Refuting the "
                    + "restricted assertion refutes the one as written.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("range-refuted", "The range fails", "result",
                ResultFormula(),
                "Take the first parameter three and the second two, so the recurrence adds three "
                    + "times the previous term to twice the one before, and take the modulus "
                    + "thirteen. The terms are zero, one, three, eleven, zero, nine, one, eight, "
                    + "zero, three, nine, seven, and the pair of consecutive terms then returns "
                    + "to zero and one, so the period is twelve. The entry point is four, since "
                    + "the fourth term is thirty-nine and the first, second and third terms are "
                    + "one, three and eleven. Twelve divided by four is three, which is larger "
                    + "than two, while two is neither one nor minus one and three exceeds two by "
                    + "one, so the pair satisfies the hypothesis. The failure is not isolated: "
                    + "the same happens for the parameters seven and six at the modulus five and "
                    + "for four and three at the modulus five. What makes the order small in "
                    + "this region is that the characteristic polynomial has one or minus one "
                    + "among its roots, which happens when the second parameter is one more than "
                    + "the first, or one less than the first with the opposite sign; the "
                    + "hypothesis as written keeps only the second of these two shapes and so "
                    + "admits pairs whose roots are irrational.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("pisano-order-range-refutation"),
                    ResolutionKind.Refuted))),
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

    private static Formula Integers() => new Formula.Integers();

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Units() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Units"));

    private static Formula Order(Formula p, Formula q) =>
        Seq(F.Id("pisanoOrder"), Open, p, Comma, Sp, q, Close);

    private static Formula Period(Formula p, Formula q) =>
        Seq(F.Id("matrixPeriod"), Open, p, Comma, Sp, q, Close);

    private static Formula Entry(Formula p, Formula q) =>
        Seq(F.Id("entryPoint"), Open, p, Comma, Sp, q, Close);

    private static Formula Abs(Formula x) => new Formula.Absolute(x);

    private static Formula OrderFormula()
    {
        var p = F.Id("p");
        var q = F.Id("q");
        return Disp(Equal(Order(p, q),
            new Formula.Fraction(Period(p, q), Entry(p, q))));
    }

    private static Formula ThreeElementSet() =>
        Seq(OpenBrace, D(0), Comma, Sp, D(1), Comma, Sp, D(2), CloseBrace);

    private static Formula ClaimFormula()
    {
        var a = F.Id("a");
        var b = F.Id("b");
        var m = F.Id("m");
        var q = F.Id("q");
        var hypothesis = And(Less(D(1), m),
            And(NotEqual(b, D(1)),
                And(NotEqual(b, new Formula.Negate(D(1))),
                    And(Equal(Abs(a), Add(Abs(b), D(1))),
                        Equal(q, new Formula.Negate(b))))));
        var conclusion = MemberOf(Order(a, q), ThreeElementSet());
        var body = Universal("a", Integers(),
            Universal("b", Integers(),
                Universal("m", Naturals(),
                    Universal("q", Units(), Implies(hypothesis, conclusion)))));
        return Disp(Iff(F.Id("claim"), body));
    }

    private static Formula ResultFormula() =>
        Disp(new Formula.Not(Parenthesized(F.Id("claim"))));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Universal(string name, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula MemberOf(Formula element, Formula set) =>
        new Formula.Relation(element, FormulaRelationOperator.MemberOf, set);

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
