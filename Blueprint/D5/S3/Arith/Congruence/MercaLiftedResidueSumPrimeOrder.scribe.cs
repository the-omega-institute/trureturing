using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class MercaLiftedResidueSumPrimeOrderDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Congruence/MercaLiftedResidueSumPrimeOrder.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/merca2011sums");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Merca's lifted residue sum over an even multiplicative-order cycle for a prime modulus.",
        H("Merca's Lifted Residue Sum at Prime Order"),
        Blocks(
            Paragraph(Text("All variables lie in the natural numbers. The operator mod returns "
                + "the least non-negative remainder, and the sum includes both endpoints.")),
            Node("liftedSum", "Lifted residue sum", LiftedSumFormula(),
                "The summand is the least non-negative remainder of the whole quantity "
                    + "2a^i+m modulo 2m, bracketed as the printed display brackets it. "
                    + "The upper bound is Mathlib's multiplicative order of "
                    + "the residue class of a modulo m: the least positive n for which a^n "
                    + "equals one modulo m, and zero if there is no such n. On the claim's "
                    + "prime, coprime domain, a has finite positive order, so the zero convention "
                    + "is not reached.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Merca's Conjecture 2", ClaimFormula(),
                "Conjecture 2 states verbatim: Let a and m be relatively prime positive integers. "
                    + "If m is prime and ord_m(a) is even then "
                    + "Σ_{i=1}^{ord_m(a)} ((2a^i + m) mod 2m) = m · ord_m(a). "
                    + "Here ord_m(a) is represented by Mathlib's orderOf on the residue class "
                    + "of a modulo m; primality supplies positivity of m.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Conjecture 2", ResultFormula(),
                "Write the even order as 2s. In the field modulo m, the s-th power of a "
                    + "squares to one but is not one, so it is minus one. Each residue at i "
                    + "then pairs with the residue at i+s, and the two lifted terms sum to 2m. "
                    + "Summing the s pairs gives m times the full order.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("merca-2011-lifted-residue-sum-prime-order"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("merca-lifted-residue-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula LiftedTerm(Formula m, Formula a, Formula i) =>
        Call("mod", Add(Multiply(Num(2), Power(a, i)), m), Multiply(Num(2), m));

    private static Formula LiftedSumValue(Formula m, Formula a)
    {
        Formula i = F.Id("i");
        return Seq(new Formula.Subscript(Sum, Equal(i, Num(1))), Caret,
            Grp(Order(m, a)), Sp, LiftedTerm(m, a, i));
    }

    private static Formula LiftedSumFormula()
    {
        Formula m = F.Id("m");
        Formula a = F.Id("a");
        return Disp(ForAll([Bound("m", Naturals()), Bound("a", Naturals())],
            Equal(Call("liftedSum", m, a), LiftedSumValue(m, a))));
    }

    private static Formula ClaimBody()
    {
        Formula a = F.Id("a");
        Formula m = F.Id("m");
        Formula order = Order(m, a);
        Formula conclusion = Equal(Call("liftedSum", m, a), Multiply(m, order));
        return ForAll([Bound("a", Naturals()), Bound("m", Naturals())],
            Implies(Less(Num(0), a),
                Implies(Call("Prime", m),
                    Implies(Call("Coprime", a, m),
                        Implies(Call("Even", order), conclusion)))));
    }

    private static Formula ClaimFormula() =>
        Disp(Iff(F.Id("claim"), ClaimBody()));

    private static Formula ResultFormula() => Disp(F.Id("claim"));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula ZMod(Formula modulus) => Call("ZMod", modulus);
    private static Formula Order(Formula m, Formula a) => Call("orderOf", Typed(a, ZMod(m)));
}
