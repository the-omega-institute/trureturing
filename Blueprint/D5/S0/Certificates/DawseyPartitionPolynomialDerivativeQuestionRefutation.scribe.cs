using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class DawseyPartitionPolynomialDerivativeQuestionRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/DawseyPartitionPolynomialDerivativeQuestionRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/dawsey2022partitionpolynomial");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The partitions (1,1) and (2) refute the printed derivative-separation question.",
        H("Dawsey--Russell--Urban Partition Polynomial Derivative Question"),
        Blocks(
            Node("dawsey-partition-polynomial", "The partition polynomial",
                PartitionPolynomialFormula(),
                "For a partition l of n, the integer polynomial is the multiset sum of "
                    + "X^i over all parts i of l. Repeated equal parts contribute repeated "
                    + "monomials, so a part i of multiplicity m_i contributes m_i times X^i.",
                "partitionPolynomial", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("dawsey-largest-part", "The largest part",
                LargestPartFormula(),
                "The value largestPart(l) is the supremum of the multiset of parts, hence "
                    + "the largest part of a nonempty partition and zero for the empty "
                    + "partition of zero.",
                "largestPart", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("dawsey-question-nine", "Question 9 as printed",
                ClaimFormula(),
                "Question 9 asks: \"If λ, λ′ are any two unequal partitions, is it true "
                    + "that f_λ^{(d)}(1) ≠ f_{λ′}^{(d)}(1) for some positive integer "
                    + "d ≤ min{lg(λ), lg(λ′)}?\" The superscript (d) denotes the d-th "
                    + "formal derivative. The quantifiers permit different sizes and lengths.",
                "claim", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("dawsey-question-nine-refuted", "The printed question has a negative answer",
                ResultFormula(),
                "The unequal partitions (1,1) and (2) both partition 2. Their largest "
                    + "parts are 1 and 2, so the only admissible positive derivative order "
                    + "is 1. Their partition polynomials are 2X and X^2, and both first "
                    + "derivatives evaluate to 2 at 1. This refutes the printed universal "
                    + "assertion and makes no claim about the same-length reading.",
                "result", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "dawsey-russell-urban-partition-polynomial-derivative-question-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(
        string id,
        string title,
        Formula formula,
        string prose,
        string declaration,
        DescribeRole role,
        AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula PartitionPolynomialFormula()
    {
        var n = F.Id("n");
        var l = F.Id("l");
        var i = F.Id("i");
        var statement = Equal(
            Call("partitionPolynomial", l),
            Seq(
                Sum, Underscore,
                Grp(i, Sp, InMacro, Sp, Call("parts", l)), Sp,
                new Formula.Power(F.Id("X"), i)));
        return Disp(Universal("n", Naturals(),
            Universal("l", Partition(n), statement)));
    }

    private static Formula LargestPartFormula()
    {
        var n = F.Id("n");
        var l = F.Id("l");
        var statement = Equal(
            Call("largestPart", l),
            Call("sup", Call("parts", l)));
        return Disp(Universal("n", Naturals(),
            Universal("l", Partition(n), statement)));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n");
        var m = F.Id("m");
        var l = F.Id("l");
        var r = F.Id("r");
        var d = F.Id("d");

        var unequalPartitions = NotEqual(Call("parts", l), Call("parts", r));
        var derivativeValuesDiffer = NotEqual(
            DerivativeAtOne(l, d), DerivativeAtOne(r, d));
        var derivativeOrder = Existential("d", Naturals(), And(
            LessThan(D(0), d),
            LessThanOrEqual(
                d, Call("min", Call("largestPart", l), Call("largestPart", r))),
            derivativeValuesDiffer));
        var quantified = Universal("n", Naturals(),
            Universal("m", Naturals(),
                Universal("l", Partition(n),
                    Universal("r", Partition(m),
                        Implies(unequalPartitions, derivativeOrder)))));
        return Disp(Iff(F.Id("claim"), quantified));
    }

    private static Formula ResultFormula() =>
        Disp(new Formula.Not(F.Id("claim")));

    private static Formula DerivativeAtOne(Formula partition, Formula order) =>
        Seq(
            new Formula.Power(
                Call("partitionPolynomial", partition),
                Parenthesized(order)),
            Parenthesized(D(1)));

    private static Formula Partition(Formula size) =>
        QualifiedCall("Nat", "Partition", size);

    private static Formula Universal(string variable, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(variable),
            domain,
            body);

    private static Formula Existential(string variable, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create(variable),
            domain,
            body);

    private static Formula And(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (int index = clauses.Length - 2; index >= 0; index--)
            result = new Formula.Logic(
                Parenthesized(clauses[index]), FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessThanOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula QualifiedCall(
        string prefix,
        string name,
        params Formula[] arguments) =>
        new Formula.Apply(Seq(F.Id(prefix), Dot, F.Id(name)), [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Parenthesized(Formula value) =>
        Seq(Open, value, Close);

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
}
