using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class AlternatingFloorSqrtZeroBlocksDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit disjoint zero blocks for alternating floor square-root differences.",
        H("Alternating Floor Square-Root Zero Blocks"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("alternating-floor-sqrt-d"),
                DeclarationHandle.Create("D5/S1/Digit/AlternatingFloorSqrtZeroBlocks.d"),
                H("The natural floor difference"),
                StatementSource.FromAuthor(DifferenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The function is defined on natural n and l. Nat.sqrt is the natural "
                    + "square root. Every subtraction in this formula is "
                    + "truncated natural subtraction, including 2*l-1 and the outer difference. "
                    + "Equation (2.3) of arXiv:2510.26291 assumes n odd, n at least one, "
                    + "and 1<=l<=div(n-1,2). Lean extends d to all natural n and l, and the "
                    + "next theorem proves the floor identity for every l at least one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("alternating-floor-sqrt-start"),
                DeclarationHandle.Create("D5/S1/Digit/AlternatingFloorSqrtZeroBlocks.blockStart"),
                H("The explicit start function"),
                StatementSource.FromAuthor(StartFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The operator div denotes natural-number division, so div(n-1,2) "
                    + "is the half-range h. The displayed label a is Lean's lam. Both n-1 "
                    + "and the subtraction of Nat.sqrt are "
                    + "truncated natural subtractions. The formula is left-associated before "
                    + "the final subtraction. The zero-block theorem proves this start positive "
                    + "and its whole block within the half-range for every eligible label."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("alternating-floor-sqrt-fidelity"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/AlternatingFloorSqrtZeroBlocks.d_eq_floor_real_sqrt"),
                H("Fidelity to real square-root floors"),
                StatementSource.FromAuthor(FidelityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The operators int and real are the canonical inclusions of natural "
                    + "numbers into the integers and reals. The square roots here are real, "
                    + "the floor values are integers, and both displayed subtractions on "
                    + "the right use their ordinary real or integer arithmetic. This "
                    + "bind-only encoding companion uses Real.floor_real_sqrt_eq_nat_sqrt "
                    + "and monotonicity. It is a separate interpretation theorem that can "
                    + "be combined with conjecture21; the Lean proof of conjecture21 itself "
                    + "depends on zero_block and blocks_disjoint."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("alternating-floor-sqrt-witness"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/AlternatingFloorSqrtZeroBlocks.witness_bounds"),
                H("Complementary indices share one square-root interval"),
                StatementSource.FromAuthor(WitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "All variables and arithmetic in this statement are natural; every "
                    + "subtraction is truncated. The label a is Lean's lam. The let-bound l is the complementary "
                    + "index h+1+lam-k. The two square inequalities have slacks "
                    + "2*lam*n-k^2 and (k-1)^2-(2*lam-1)*n respectively, interpreted "
                    + "as integer differences: the first is nonnegative and the second "
                    + "strictly positive. This is the preregistered witness of candidate "
                    + "theorem 4.109. The dependency direction is conjecture21 to "
                    + "witness_bounds, through the zero and disjointness clauses."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("alternating-floor-sqrt-block-point"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/AlternatingFloorSqrtZeroBlocks.block_point"),
                H("Every block offset has two equal complementary roots"),
                StatementSource.FromAuthor(BlockPointFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "All variables and arithmetic are natural, and every subtraction is "
                    + "truncated. For each permitted offset j, the theorem exposes a "
                    + "complementary index k at most n, its label equation, and the two "
                    + "root equalities required by the atom. The dependency direction is "
                    + "zero_block and blocks_disjoint to block_point."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("alternating-floor-sqrt-zero-block"),
                DeclarationHandle.Create("D5/S1/Digit/AlternatingFloorSqrtZeroBlocks.zero_block"),
                H("Every entry of the consecutive block vanishes"),
                StatementSource.FromAuthor(ZeroFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every variable is natural; a is Lean's lam. Subtraction in d, blockStart, and d(n,lam)-2 "
                    + "is truncated natural subtraction; j begins at zero. The hypothesis "
                    + "d(n,lam) at least two makes the displayed inclusive block have "
                    + "d(n,lam)-1 entries. Both roots at each entry equal n-k by witness_bounds. "
                    + "This is the consecutive-zero and range clause of candidate theorem "
                    + "4.109, with dependency direction conjecture21 to zero_block."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("alternating-floor-sqrt-label-recovery"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/AlternatingFloorSqrtZeroBlocks.common_index_label_recovery"),
                H("A common index recovers its label"),
                StatementSource.FromAuthor(CommonIndexLabelRecoveryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "All variables and arithmetic are natural, and subtraction is truncated. "
                    + "The bounds on k and j make equality of n-k and n-j recover k=j; the "
                    + "two common-index label equations then recover a=b. The dependency "
                    + "direction is blocks_disjoint to common_index_label_recovery."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("alternating-floor-sqrt-disjoint"),
                DeclarationHandle.Create(
                    "D5/S1/Digit/AlternatingFloorSqrtZeroBlocks.blocks_disjoint"),
                H("Distinct eligible labels have disjoint index blocks"),
                StatementSource.FromAuthor(DisjointFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "All variables are natural; a and b are Lean's lam and mu. All subtractions in d, blockStart, "
                    + "and the endpoints are truncated natural subtraction. False means "
                    + "that no index l can satisfy all four membership bounds. A shared "
                    + "floor value forces equal complementary indices, then equal labels. "
                    + "This is the disjointness clause of candidate theorem 4.109, with "
                    + "dependency direction conjecture21 to blocks_disjoint."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("alternating-floor-sqrt-conjecture"),
                DeclarationHandle.Create("D5/S1/Digit/AlternatingFloorSqrtZeroBlocks.conjecture21"),
                H("The full simultaneous zero-block theorem"),
                StatementSource.FromAuthor(ConjectureFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "This proves the whole statement registered as candidate theorem "
                        + "4.109: one start function simultaneously supplies every eligible "
                        + "label's consecutive zero block and makes distinct blocks disjoint. "
                        + "The proof chooses s(lam)=blockStart(n,lam). All quantified values "
                        + "are natural; a and b are Lean's lam and mu. "
                        + "The operator div is natural-number division, and "
                        + "every subtraction in this display and in d is truncated natural "
                        + "subtraction. The positive-index floor identity above supplies "
                        + "the real-floor interpretation, including at all produced indices.")),
                    Paragraph(Text(
                        "The conjecture's source is Chamberland and Dilcher, "
                        + "arXiv:2510.26291v1, section 2, equation (2.3) and Conjecture 2.1. "
                        + "That paper states that its proof is incomplete; it is the source "
                        + "of the problem, not an attestation of the proof given here. "
                        + "The range of labels is the definition's range from one through "
                        + "div(n-1,2). Disjointness refers to index intervals."))),
                DescribeRole.Theorem))));

    private static Formula DifferenceFormula()
    {
        Formula n = F.Id("n"), l = F.Id("l");
        return Disp(All(["n", "l"], Equal(Difference(n, l),
            Subtract(Root(Upper(n, l)), Root(Lower(n, l))))));
    }

    private static Formula StartFormula()
    {
        Formula n = F.Id("n"), lam = F.Id("a");
        return Disp(All(["n", "a"], Equal(Start(n, lam),
            Subtract(Add(Add(Half(n), D(1)), lam), Root(Upper(n, lam))))));
    }

    private static Formula FidelityFormula()
    {
        Formula n = F.Id("n"), l = F.Id("l");
        Formula rn = Call("real", n), rl = Call("real", l);
        Formula rhs = Subtract(
            new Formula.Floor(Seq(Sqrt, Grp(Upper(rn, rl)))),
            new Formula.Floor(Seq(Sqrt, Grp(Lower(rn, rl)))));
        return Disp(All(["n", "l"], Imp(Le(D(1), l),
            Equal(Call("int", Difference(n, l)), rhs))));
    }

    private static Formula WitnessFormula()
    {
        Formula n = F.Id("n"), h = F.Id("h"), lam = F.Id("a");
        Formula k = F.Id("k"), l = F.Id("l");
        Formula assumptions = And(
            OddRepresentation(n, h), Le(D(1), lam), Le(lam, h),
            Le(Add(Root(Lower(n, lam)), D(2)), k), Le(k, Root(Upper(n, lam))));
        Formula bounds = And(
            Le(D(1), l), Le(l, h), Le(k, n),
            Le(Square(Subtract(n, k)), Lower(n, l)),
            Le(Lower(n, l), Upper(n, l)),
            Less(Upper(n, l), Square(Add(Subtract(n, k), D(1)))));
        Formula body = Seq(F.Id("let"), Sp, l, Sp, Colon, Eq, Sp,
            Subtract(Add(Add(h, D(1)), lam), k), Sp, F.Id("in"), Sp, bounds);
        return Disp(All(["n", "h", "a", "k"], Imp(assumptions, body)));
    }

    private static Formula ZeroFormula()
    {
        Formula n = F.Id("n"), h = F.Id("h"), lam = F.Id("a");
        return Disp(All(["n", "h", "a"], Imp(
            And(OddRepresentation(n, h), Eligible(n, h, lam)),
            ZeroClause(n, h, lam, Start(n, lam)))));
    }

    private static Formula BlockPointFormula()
    {
        Formula n = F.Id("n"), h = F.Id("h"), lam = F.Id("a");
        Formula j = F.Id("j"), k = F.Id("k");
        Formula index = Add(Start(n, lam), j);
        Formula witness = new Formula.Bind(
            FormulaQuantifier.Exists, FormulaIdentifier.Create("k"), Naturals(),
            And(Le(k, n), Equal(Add(index, k), Add(Add(h, D(1)), lam)),
                Equal(Root(Lower(n, index)), Subtract(n, k)),
                Equal(Root(Upper(n, index)), Subtract(n, k))));
        return Disp(All(["n", "h", "a", "j"], Imp(
            And(OddRepresentation(n, h), Eligible(n, h, lam), Le(j, Width(n, lam))),
            And(Le(D(1), index), Le(index, h), witness))));
    }

    private static Formula DisjointFormula()
    {
        Formula n = F.Id("n"), h = F.Id("h");
        Formula lam = F.Id("a"), mu = F.Id("b");
        return Disp(All(["n", "h", "a", "b"], Imp(
            And(OddRepresentation(n, h), Eligible(n, h, lam), Eligible(n, h, mu),
                NotEqual(lam, mu)),
            NoCommonIndex(n, lam, mu, Start(n, lam), Start(n, mu)))));
    }

    private static Formula CommonIndexLabelRecoveryFormula()
    {
        Formula n = F.Id("n"), h = F.Id("h"), lam = F.Id("a"), mu = F.Id("b");
        Formula l = F.Id("l"), k = F.Id("k"), j = F.Id("j");
        return Disp(All(["n", "h", "a", "b", "l", "k", "j"], Imp(
            And(Le(k, n), Le(j, n),
                Equal(Add(l, k), Add(Add(h, D(1)), lam)),
                Equal(Add(l, j), Add(Add(h, D(1)), mu)),
                Equal(Subtract(n, k), Subtract(n, j))),
            And(Equal(k, j), Equal(lam, mu)))));
    }

    private static Formula ConjectureFormula()
    {
        Formula n = F.Id("n"), lam = F.Id("a"), mu = F.Id("b");
        Formula zero = All(["a"], Imp(Eligible(n, Half(n), lam),
            ZeroClause(n, Half(n), lam, new Formula.Apply(F.Id("s"), [lam]))));
        Formula disjoint = All(["a", "b"], Imp(
            And(Eligible(n, Half(n), lam), Eligible(n, Half(n), mu), NotEqual(lam, mu)),
            NoCommonIndex(n, lam, mu, new Formula.Apply(F.Id("s"), [lam]),
                new Formula.Apply(F.Id("s"), [mu]))));
        Formula starts = new Formula.Bind(FormulaQuantifier.Exists,
            FormulaIdentifier.Create("s"), new Formula.TypeArrow(Naturals(), Naturals()),
            And(zero, disjoint));
        return Disp(All(["n"], Imp(And(Le(D(1), n), Call("Odd", n)), starts)));
    }

    private static Formula ZeroClause(Formula n, Formula h, Formula lam, Formula start)
    {
        Formula j = F.Id("j");
        return And(Le(D(1), start), Le(Add(start, Width(n, lam)), h),
            All(["j"], Imp(Le(j, Width(n, lam)),
                Equal(Difference(n, Add(start, j)), D(0)))));
    }

    private static Formula NoCommonIndex(
        Formula n, Formula lam, Formula mu, Formula first, Formula second)
    {
        Formula l = F.Id("l");
        return All(["l"], Imp(
            And(Le(first, l), Le(l, Add(first, Width(n, lam))),
                Le(second, l), Le(l, Add(second, Width(n, mu)))), F.Id("False")));
    }

    private static Formula Eligible(Formula n, Formula h, Formula lam) =>
        And(Le(D(1), lam), Le(lam, h), Le(D(2), Difference(n, lam)));

    private static Formula OddRepresentation(Formula n, Formula h) =>
        Equal(n, Add(Multiply(D(2), h), D(1)));

    private static Formula Difference(Formula n, Formula l) => Call("d", n, l);
    private static Formula Start(Formula n, Formula l) => Call("blockStart", n, l);
    private static Formula Width(Formula n, Formula l) =>
        Parenthesized(Subtract(Difference(n, l), D(2)));
    private static Formula Half(Formula n) => Call("div", Subtract(n, D(1)), D(2));
    private static Formula Upper(Formula n, Formula l) => Multiply(Multiply(D(2), l), n);
    private static Formula Lower(Formula n, Formula l) =>
        Multiply(Parenthesized(Subtract(Multiply(D(2), l), D(1))), n);
    private static Formula Root(Formula x) =>
        new Formula.Apply(Seq(F.Id("Nat"), Dot, F.Id("sqrt")), [x]);
    private static Formula Square(Formula x) => new Formula.Power(Parenthesized(x), D(2));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Le(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Less(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Imp(Formula x, Formula y) =>
        new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Implies, Parenthesized(y));

    private static Formula And(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (int i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(Parenthesized(clauses[i]), FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula All(string[] names, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. names.Select(name => new Formula.BoundVariable(FormulaIdentifier.Create(name), Naturals()))],
            body);
}
