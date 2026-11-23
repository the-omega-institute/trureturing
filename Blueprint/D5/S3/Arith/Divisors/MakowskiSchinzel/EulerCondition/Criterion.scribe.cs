using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors.MakowskiSchinzel.EulerCondition;

internal sealed class EulerConditionCriterionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Divisors/MakowskiSchinzel/EulerCondition/Criterion.";
    private static readonly LibraryNoteRef Cohen =
        LibraryNoteRef.Create("D5/L/ArithUnits/cohen1997makowski");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The odd predecessor criterion", H("The odd predecessor criterion"), Blocks(
            Node("oddPredecessorPart", "The odd predecessor part", All("n", Nat(),
                Eq(Call("oddPredecessorPart", V("n")), Call("ordCompl", D(2),
                    Prod("q", Call("nonFermatFactors", V("n")), Sub(V("q"), D(1)))))),
                "Take the odd part of the product of q-1 over the distinct non-Fermat " +
                "odd prime divisors q of n. The empty product gives the value 1.", true),
            Node("psi", "The predecessor abundancy factor", All("n", Nat(),
                Eq(Call("psi", V("n")), Mul(Call("abundancyIndex",
                    Call("oddPredecessorPart", V("n"))), Prod("q",
                    Call("nonFermatFactors", V("n")), Sub(D(1), Div(D(1), V("q"))))))),
                "Multiply the odd predecessor part's abundancy index by the Euler " +
                "factors 1-1/q of the non-Fermat support. This factor is positive for " +
                "every natural input.", true),
            Node("psi_mul_le_sigma_totient", "A direct sigma-totient lower bound", Criterion(),
                "For every natural n, psi(n)n is at most twice sigma(phi(n)); the " +
                "factor two is omitted for odd n. Both comparisons are strict when " +
                "the non-Fermat support is nonempty. Zero is included. The constants " +
                "are sharp: n=2 gives equality in the first comparison and n=1 in the " +
                "odd comparison. These examples also prevent unconditional strictness. " +
                "The proof passes to the odd squarefree core. Its Fermat part f has " +
                "power-of-two totient, while the odd predecessor part U is coprime " +
                "to that totient. Divisibility by phi(f)U gives the weak bound; a " +
                "nonempty non-Fermat support contributes another factor of two and " +
                "gives the strict improvement of the power-of-two abundancy index. " +
                "This also recovers the sufficient condition in Cohen's 1997 " +
                "Theorem 3. Choose an odd prime r_i dividing q_i-1 for each non-Fermat " +
                "q_i, and group equal choices with sizes c_j. Then the product " +
                "R of the r_i divides U. Hence psi is at least the product of " +
                "geom(r_j,c_j) times the group's factors (q-1)/q. Cohen's group " +
                "conditions make this product at least 1. When the non-Fermat " +
                "support is nonempty, the strict comparison gives sigma(phi(m))>m " +
                "for the odd input. Thus the group conditions imply psi>=1; " +
                "no converse is asserted."))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, bool definition = false) => Describe.Lean(
        DescribeId.Create("euler-condition-criterion-" +
            name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Cohen),
        Blocks(Paragraph(Text(prose))),
        definition ? DescribeRole.Definition : DescribeRole.Theorem);

    private static Formula Criterion()
    {
        var n = V("n");
        var lhs = Mul(Call("psi", n), n);
        var sigma = Call("sigma", D(1), Call("totient", n));
        var odd = Call("Odd", n);
        var strict = Imp(Call("Nonempty", Call("nonFermatFactors", n)),
            And(Lt(lhs, Mul(D(2), sigma)), Imp(odd, Lt(lhs, sigma))));
        return All("n", Nat(), And(Le(lhs, Mul(D(2), sigma)),
            And(Imp(odd, Le(lhs, sigma)), strict)));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Prod(string name, Formula set, Formula body) =>
        Seq(new Formula.Subscript(F.Prod, Seq(V(name), Sp, InMacro, Sp, set)),
            Sp, Seq(Open, body, Close));
}
