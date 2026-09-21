using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class MercaResidueSumEvenOrderRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/MercaResidueSumEvenOrderRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/merca2011sums");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Merca's printed even-order residue-sum conjecture fails for a = 2 and m = 15.",
        H("Merca's Even-Order Residue-Sum Conjecture"),
        Blocks(
            Node(
                "merca-residue-sum",
                "Residue sum through the multiplicative order",
                "residueSum",
                ResidueSumFormula(),
                "The sum ranges over every natural index i from 1 through "
                    + "orderOf (a : ZMod m), inclusive. Each summand is the least non-negative "
                    + "remainder of a^i modulo m. Here orderOf (a : ZMod m) is Mathlib's "
                    + "multiplicative order of the residue class of a modulo m: the least "
                    + "positive n with a^n congruent to 1 modulo m, and zero when no such n "
                    + "exists. It is the paper's ord_m(a) from page 17. The zero convention is "
                    + "never reached on the claim's domain.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "merca-conjecture-one",
                "Conjecture 1",
                "claim",
                ClaimFormula(),
                "The paper states: \"Conjecture 1. Let a and m be relatively prime positive "
                    + "integers. If a−1 and m are relatively prime and ord_m(a) is even then "
                    + "Σ_{i=1}^{ord_m(a)} (a^i mod m) = m · ord_m(a) / 2.\" The displayed "
                    + "formal equality doubles both sides. This is exact because "
                    + "orderOf (a : ZMod m) is even, so m times the order is divisible by "
                    + "two. Subtraction is natural subtraction and a is positive.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "merca-conjecture-one-refuted",
                "Conjecture 1 is false",
                "result",
                ResultFormula(),
                "At a = 2 and m = 15, both coprimality conditions hold and "
                    + "orderOf (2 : ZMod 15) = 4. "
                    + "The residues are 2, 4, 8, and 1, with sum 15. The conjecture's right "
                    + "side is 15 * 4 / 2 = 30, so the universal claim is false.",
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(
        string id,
        string title,
        string declaration,
        Formula formula,
        string prose,
        DescribeRole role,
        AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role,
            resolution);

    private static Formula ResidueSumFormula()
    {
        var m = F.Id("m");
        var a = F.Id("a");
        var i = F.Id("i");
        var order = Order(m, a);
        var summand = new Formula.Modulo(Power(a, i), m);
        var definition = Equal(
            Call("residueSum", m, a),
            BoundedSum(i, D(1), order, summand));
        return Disp(Universal(["m", "a"], definition));
    }

    private static Formula ClaimFormula()
    {
        var a = F.Id("a");
        var m = F.Id("m");
        var order = Order(m, a);
        var equality = Equal(
            Multiply(D(2), Call("residueSum", m, a)),
            Multiply(m, order));
        var body = Implies(Less(D(0), a),
            Implies(Less(D(0), m),
                Implies(QualifiedCall("Nat", "Coprime", a, m),
                    Implies(QualifiedCall("Nat", "Coprime", Subtract(a, D(1)), m),
                        Implies(Call("Even", order), equality)))));
        return Disp(Iff(F.Id("claim"), Universal(["a", "m"], body)));
    }

    private static Formula ResultFormula() =>
        Disp(new Formula.Not(F.Id("claim")));

    private static Formula Universal(string[] names, Formula body) =>
        new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [.. names.Select(name => new Formula.BoundVariable(
                FormulaIdentifier.Create(name), Naturals()))],
            body);

    private static Formula BoundedSum(
        Formula index,
        Formula lower,
        Formula upper,
        Formula summand) =>
        Seq(new Formula.Subscript(F.Sum, Equal(index, lower)),
            Caret, Grp(upper), Sp, Parenthesized(summand));

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula QualifiedCall(
        string prefix,
        string name,
        params Formula[] arguments) =>
        new Formula.Apply(Seq(F.Id(prefix), Dot, F.Id(name)), [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Order(Formula modulus, Formula value) =>
        Call("orderOf", Typed(value, ZMod(modulus)));

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula ZMod(Formula modulus) => Call("ZMod", modulus);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
}
