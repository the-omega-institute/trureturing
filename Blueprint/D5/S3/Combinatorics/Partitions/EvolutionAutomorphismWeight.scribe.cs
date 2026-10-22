using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class EvolutionAutomorphismWeightDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/EvolutionAutomorphismWeight.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The multiplicity weight of a positive integer partition has six exceptional maxima and equals the factorial maximum from dimension seven onward. The maxima absorb a factorial of the remaining dimension with a shift by one.",
        H("Sharp multiplicity weights of integer partitions"),
        Blocks(
            Node("weight", "Multiplicity weight", "weight", DescribeRole.Definition, WeightFormula(),
                "For a multiset of natural parts, multiply once for each distinct part l. If l occurs m times, its factor is (l times (2 to the l minus one)) to the m times m factorial. Parts equal to one are retained: their factor is the factorial of their multiplicity."),
            Node("maximum", "Maximum over positive partitions", "maximumWeight", DescribeRole.Definition, MaximumFormula(),
                "The maximum is the finite supremum over Mathlib's Nat.Partition n. Its parts are positive and sum to n. The existing finite supremum attainment theorem gives an attaining partition, including at the neutral dimension zero."),
            Node("factorial-bound", "The factorial bound", "weight_le_factorial", DescribeRole.Theorem, BoundFormula(),
                "For each positive part l at least six, l times (2 to the l minus one) is at most l factorial. Mathlib's uniformBell_mul_eq lifts this estimate to each multiplicity group. For lengths two, three, four and five, the factorial estimate starts at multiplicities four, three, two and two respectively; choose_mul_add propagates it. A numerical majorant with the six exceptional values is supermultiplicative. Combining distinct groups therefore bounds the complete partition weight by that majorant at the sum of the parts."),
            Node("small-maxima", "The six exceptional maxima", "maximum_weight_small", DescribeRole.Theorem, SmallFormula(),
                "The partitions [1], [2], [3], [2,2], [5] and [2,2,2] attain the six displayed values. The same general majorant supplies their upper bounds."),
            Node("factorial-maximum", "The factorial maximum", "maximum_weight_eq_factorial", DescribeRole.Theorem, SharpFormula(),
                "The partition with n parts equal to one has weight n factorial. This lower bound meets the universal upper bound for every n at least seven."),
            Node("absorption", "Absorbing the remaining dimension", "maximum_weight_mul_factorial_le", DescribeRole.Theorem, AbsorptionFormula(),
                "The inequality holds for every pair of positive dimensions s at most n, with the factorial of n minus s plus one. Equality handles s equal to n; s equal to one uses the all-ones lower bound. For the remaining dimensions, compare the maximum in dimension s to n descending factorial of length s minus one and use factorial_mul_descFactorial. This arithmetic statement does not identify a partition of s with a partition of n and makes no assertion about algebra automorphisms.")),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        DescribeRole role, Formula formula, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, Seq(Open, b, Close));
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, Seq(Open, b, Close));
    private static Formula Fact(Formula a) => Seq(a, Bang);
    private static Formula NatType => F.Id("Nat");
    private static Formula W(Formula p) => Call("weight", p);
    private static Formula M(Formula n) => Call("maximumWeight", n);
    private static Formula Parts(Formula p) => Call("parts", p);
    private static Formula Part(Formula n) => Call("Partition", n);

    private static Formula WeightFormula()
    {
        Formula p = F.Id("p"), l = F.Id("l"), m = Call("count", p, l);
        Formula factor = Seq(Open, l, Cdot, Open, new Formula.Power(D(2), l),
            Minus, D(1), Close, Close);
        Formula domain = new Formula.Relation(l, FormulaRelationOperator.MemberOf, Call("toFinset", p));
        return Disp(All("p", Call("Multiset", NatType), Eq(W(p),
            Seq(new Formula.Subscript(Prod, domain), Open, new Formula.Power(factor, m), Cdot, Fact(m), Close))));
    }

    private static Formula MaximumFormula()
    {
        Formula n = F.Id("n"), p = F.Id("p");
        return Disp(All("n", NatType, Eq(M(n),
            Seq(new Formula.Subscript(Max, Seq(p, InMacro, Part(n))), W(Parts(p))))));
    }

    private static Formula BoundFormula()
    {
        Formula n = F.Id("n"), p = F.Id("p");
        return Disp(All("n", NatType, Imp(Leq(D(7), n),
            All("p", Part(n), Leq(W(Parts(p)), Fact(n))))));
    }

    private static Formula SmallFormula() => Disp(And(Eq(M(D(1)), D(1)),
        And(Eq(M(D(2)), D(6)), And(Eq(M(D(3)), D(2,1)),
        And(Eq(M(D(4)), D(7,2)), And(Eq(M(D(5)), D(1,5,5)), Eq(M(D(6)), D(1,2,9,6))))))));

    private static Formula SharpFormula()
    {
        Formula n = F.Id("n");
        return Disp(All("n", NatType, Imp(Leq(D(7), n), Eq(M(n), Fact(n)))));
    }

    private static Formula AbsorptionFormula()
    {
        Formula s = F.Id("s"), n = F.Id("n");
        return Disp(All("s", NatType, All("n", NatType, Imp(Leq(D(1), s),
            Imp(Leq(s, n), Leq(Seq(M(s), Cdot, Fact(Seq(Open, n, Minus, s, Plus, D(1), Close))), M(n)))))));
    }
}

