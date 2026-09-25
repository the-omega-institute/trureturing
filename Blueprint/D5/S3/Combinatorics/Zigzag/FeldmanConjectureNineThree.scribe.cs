using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Zigzag;

internal sealed class FeldmanConjectureNineThreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Zigzag/FeldmanConjectureNineThree.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/feldman2026missingzigzag");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both parity equivalences and finite Laurent coefficients give closed formulas for Feldman's actual balance-only count and the complete three-clause Conjecture 9.3.",
        H("Feldman's Balance-Only Conjecture 9.3"),
        Blocks(
            Paragraph(Text(
                "The published Section 5 equation (2) determines the six directed forms, the four admissible labels at k=2, and balance at every nonzero residue. Only Conjecture 9.3 is the target: neither all of Open Problem 13.1 nor Conjecture 9.2, cycle closure, or Hamiltonian existence follows from this count.")),
            Describe.Lean(DescribeId.Create("exact-even-balanced-count"),
                DeclarationHandle.Create(Prefix + "balancedCount_even_closed"),
                H("All positive even parameters"), StatementSource.FromAuthor(EvenFormula()),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(
                    "For every r>=1, the literal count balancedCount(2r) is 4*6^(r-1)*choose(2r-2,r-1). The proof converts the finite Balanced subtype through evenBalancedChoicesEquiv, uses explicit sector reflection, and extracts Laurent coefficient zero at depth 3r-3. Thus the transfer polynomial counts the actual source objects."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exact-odd-balanced-count"),
                DeclarationHandle.Create(Prefix + "balancedCount_odd_closed"),
                H("All positive odd parameters"), StatementSource.FromAuthor(OddFormula()),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(
                    "For every r>=1, balancedCount(2r+1) is 2*6^r*choose(2r-1,r). This uses oddBalancedChoicesEquiv and the independently proved singleton charge shift, extracting coefficient -1 at depth 3r-1. Its validity is not inferred from the even antipodal geometry."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-conjecture-nine-three"),
                DeclarationHandle.Create(Prefix + "feldman_conjecture_nine_three"),
                H("The three original clauses"), StatementSource.FromAuthor(ConjectureFormula()),
                AssessedProvenance.FromRepo(Source), Blocks(
                    Paragraph(Text(
                        "The sole result states balancedCount 2=4; for every r>=2, balancedCount(2r)=4*balancedCount(2r-1); and for every r>=1, (2r)*balancedCount(2r+1)=6*(2r-1)*balancedCount(2r). The proof specializes the exact even and odd formulas and uses central-binomial and adjacent-choose identities. Every parameter range is preserved.")),
                    Paragraph(Text(
                        "This is a source-reviewed Lean candidate. The typed open-problem resolution binding is deferred until the result is canonically frozen; the Problems dossier records the question and outstanding delivery boundary without hand-writing a machine resolution status."))),
                DescribeRole.Theorem)), []));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula AtLeast(Formula lower, Formula upper) =>
        new Formula.Relation(lower, FormulaRelationOperator.LessThanOrEqual, upper);
    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Universal(Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("r"),
            new Formula.NamedConstant(FormulaIdentifier.Create("Nat")), body);
    private static Formula Count(Formula argument) => Call("balancedCount", argument);
    private static Formula Choose(Formula n, Formula k) => Call("choose", n, k);
    private static Formula Pow(Formula baseValue, Formula exponent) =>
        new Formula.Power(baseValue, exponent);

    private static Formula EvenFormula()
    {
        var r = F.Id("r");
        var even = Mul(D(2), r);
        return Disp(Universal(Implies(AtLeast(D(1), r),
            Equal(Count(even), Mul(Mul(D(4), Pow(D(6), Sub(r, D(1)))),
                Choose(Sub(even, D(2)), Sub(r, D(1))))))));
    }

    private static Formula OddFormula()
    {
        var r = F.Id("r");
        var even = Mul(D(2), r);
        return Disp(Universal(Implies(AtLeast(D(1), r),
            Equal(Count(Add(even, D(1))), Mul(Mul(D(2), Pow(D(6), r)),
                Choose(Sub(even, D(1)), r))))));
    }

    private static Formula ConjectureFormula()
    {
        var r = F.Id("r");
        var even = Mul(D(2), r);
        var first = Equal(Count(D(2)), D(4));
        var second = Universal(Implies(AtLeast(D(2), r),
            Equal(Count(even), Mul(D(4), Count(Sub(even, D(1)))))));
        var third = Universal(Implies(AtLeast(D(1), r),
            Equal(Mul(even, Count(Add(even, D(1)))),
                Mul(Mul(D(6), Sub(even, D(1))), Count(even)))));
        return Disp(And(first, And(second, third)));
    }
}
