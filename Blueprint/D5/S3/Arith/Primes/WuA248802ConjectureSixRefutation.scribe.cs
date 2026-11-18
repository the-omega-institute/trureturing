using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class WuA248802ConjectureSixRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Primes/WuA248802ConjectureSixRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Factorization/wu2019a248802c6");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An admissible overlap with House's 1759 progression refutes Wu's full Conjecture 6.",
        H("Wu's full A248802 Conjecture 6 is false"),
        Blocks(
            Domain("coveredOne", "C1", Progression(10, 2),
                "C1 includes every natural parameter, including zero."),
            Domain("coveredTwo", "C2", Progression(36, 16, 1),
                "C2 retains the parameter restriction m mod 5 not equal to 1."),
            Domain("coveredThree", "C3", Progression(84, 22, 0),
                "C3 retains the parameter restriction m mod 5 not equal to 0."),
            Domain("coveredFour", "C4", And(Progression(58, 26),
                And(Neg(Call("coveredOne", V("k"))),
                    And(Neg(Call("coveredTwo", V("k"))), Neg(Call("coveredThree", V("k")))))),
                "C4 recursively excludes C1, C2 and C3 at the same index k."),
            Domain("coveredFive", "C5", Progression(138, 6, 2),
                "C5 retains the parameter restriction m mod 5 not equal to 2."),
            Describe.Lean(DescribeId.Create("wu-a248802-six-claim"),
                DeclarationHandle.Create(Prefix + "claim"), H("The original conditional universal claim"),
                StatementSource.FromAuthor(Disp(Iff(Call("claim"), ClaimFormula()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every natural n, including zero, set k=44n+10. "
                    + "If none of C1 through C5 applies, the source asserts that the natural "
                    + "least prime factor of 2^(2^k+2)+3 is 2383. All five exclusions belong "
                    + "to the claim, with the earlier predicates exactly as defined above."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("wu-a248802-six-result"),
                DeclarationHandle.Create(Prefix + "result"), H("An admissible counterexample"),
                StatementSource.FromAuthor(Disp(Neg(Call("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The witness n=79 gives k=3486=274+292*11. "
                    + "Its residues modulo (10,36,84,58,138) are (6,30,42,6,36), excluding "
                    + "every preceding domain. The modular certificate uses 2^292=1 and "
                    + "2^274=718 modulo 879, then 2^879=1 and 2^720=1756 modulo 1759. "
                    + "It proves 1759 divides 2^(2^3486+2)+3 without expanding the double "
                    + "exponential. Nat.minFac_le_of_dvd gives a(3486)<=1759<2383. "
                    + "Matthew House's MathOverflow answer and prior divisibility table "
                    + "supply the 1759 progression; the result adds the admissible "
                    + "intersection and the full claim's negation. No exact minimum "
                    + "equality or global priority is asserted."))), DescribeRole.Theorem))));

    private static ScribeNode Domain(string name, string label, Formula body, string prose) =>
        Describe.Lean(DescribeId.Create("wu-a248802-six-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(label + " coverage domain"),
            StatementSource.FromAuthor(Disp(All("k", Nat(), Iff(Call(name, V("k")), body)))),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Progression(int step, int offset, int? excluded = null)
    {
        var equality = Eqn(V("k"), Add(Mul(Num(step), V("m")), Num(offset)));
        var condition = excluded is int residue
            ? And(equality, Neg(Eqn(Call("mod", V("m"), D(5)), Num(residue)))) : equality;
        return Ex("m", Nat(), condition);
    }

    private static Formula ClaimFormula()
    {
        var k = Add(Mul(D(4,4), V("n")), D(1,0));
        Formula body = Eqn(Call("minFac", Add(new Formula.Power(D(2),
            Add(new Formula.Power(D(2), Parenthesized(k)), D(2))), D(3))), D(2,3,8,3));
        foreach (var name in new[] { "coveredFive", "coveredFour", "coveredThree", "coveredTwo", "coveredOne" })
            body = Logic(Neg(Call(name, k)), FormulaLogicOperator.Implies, body);
        return All("n", Nat(), body);
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [..args]);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Neg(Formula a) => new Formula.Not(Parenthesized(a));
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) => new Formula.Logic(Parenthesized(a), op, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Iff(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Ex(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, b);
}
