using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class MisawaHarmonicStrengthPairRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Geometry/MisawaHarmonicStrengthPairRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/misawa2025spherical");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The pair {2,4} refutes the proposed universal value five for two-element harmonic strength.",
        H("A Harmonic-Strength Pair Obstruction on the Unit Circle"),
        Blocks(
            Node(
                "misawa-complex-moment",
                "Complex moments",
                "momentSum",
                MomentSumFormula(),
                "For a finite set X of complex numbers, momentSum(X,k) is the sum of the "
                    + "k-th powers of its elements. This is P_k(X) on printed pages 2--3.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "misawa-harmonic-strength",
                "Harmonic strength",
                "harmonicStrength",
                HarmonicStrengthFormula(),
                "The harmonic strength is the set of natural indices at which the complex "
                    + "moment vanishes. This is the paper's working form of Hst(X).",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "misawa-unit-circle",
                "Finite subsets of the unit circle",
                "OnUnitCircle",
                OnUnitCircleFormula(),
                "OnUnitCircle(X) means that every member of the finite complex set X has norm one, "
                    + "matching the identification S¹ = {z ∈ ℂ | |z| = 1}.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "misawa-minimum-size",
                "Minimum size at a prescribed strength",
                "minimumSize",
                MinimumSizeFormula(),
                "minimumSize(T) is the infimum in the natural numbers of the attainable "
                    + "cardinalities of finite unit-circle sets with harmonic strength exactly T. "
                    + "The convention for an empty family is Nat.sInf_empty = 0.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "misawa-harmonic-pair-conjecture",
                "Misawa--Nishimura Conjecture 3.3",
                "claim",
                ClaimFormula(),
                "Conjecture 3.3 on printed page 6 reads verbatim: \u201cLet p ≠ q be integers with "
                    + "p, q > 1. Then N({p, q}, 2) = 5.\u201d On the same page, \u201cFor a nonempty finite "
                    + "set T ⊂ ℕ, define N(T, 2) := min{|X| | X ⊂ S¹, Hst(X) = T}.\u201d "
                    + "The formal statement uses natural p and q with the printed lower bounds.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "misawa-harmonic-pair-refutation",
                "The pair {2,4} refutes the conjecture",
                "result",
                ResultFormula(),
                "Assume a five-point unit-circle set has vanishing second and fourth moments. "
                    + "After squaring its five points, conjugation and the unit relations turn "
                    + "the first two vanishing power sums into a polynomial identity forcing the "
                    + "third power sum to vanish. Thus the original sixth moment also vanishes, "
                    + "so its harmonic strength cannot equal {2,4}. No value for minimumSize({2,4}) "
                    + "is asserted.",
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo()))));

    private static DocumentBlock Node(
        string id,
        string title,
        string declaration,
        Formula formula,
        string prose,
        DescribeRole role,
        AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role);

    private static Formula MomentSumFormula()
    {
        var x = F.Id("x");
        var X = F.Id("X");
        var k = F.Id("k");
        var sum = Seq(new Formula.Subscript(Sum, Seq(x, Sp, InMacro, Sp, X)), Sp,
            new Formula.Power(x, k));
        return Disp(ForAll("X", Finset(ComplexNumbers()),
            ForAll("k", Naturals(), Equal(Call("momentSum", X, k), sum))));
    }

    private static Formula HarmonicStrengthFormula()
    {
        var X = F.Id("X");
        var k = F.Id("k");
        var vanishing = Equal(Call("momentSum", X, k), D(0));
        var strength = Seq(OpenBrace, k, Sp, InMacro, Sp, Naturals(), Sp,
            Mid, Sp, vanishing, CloseBrace);
        return Disp(ForAll("X", Finset(ComplexNumbers()),
            Equal(Call("harmonicStrength", X), strength)));
    }

    private static Formula OnUnitCircleFormula()
    {
        var X = F.Id("X");
        var x = F.Id("x");
        var allUnit = ForAll("x", X, Equal(new Formula.Norm(x), D(1)));
        return Disp(ForAll("X", Finset(ComplexNumbers()),
            IffFormula(Call("OnUnitCircle", X), allUnit)));
    }

    private static Formula MinimumSizeFormula()
    {
        var T = F.Id("T");
        var n = F.Id("n");
        var X = F.Id("X");
        var attainable = Exists("X", Finset(ComplexNumbers()), Conjoin(
            Call("OnUnitCircle", X),
            Equal(Call("harmonicStrength", X), T),
            Equal(Call("card", X), n)));
        var sizes = Seq(OpenBrace, n, Sp, InMacro, Sp, Naturals(), Sp,
            Mid, Sp, attainable, CloseBrace);
        return Disp(ForAll("T", SetOf(Naturals()),
            Equal(Call("minimumSize", T), Call("sInf", sizes))));
    }

    private static Formula ClaimFormula()
    {
        var p = F.Id("p");
        var q = F.Id("q");
        var quantified = ForAll("p", Naturals(), ForAll("q", Naturals(),
            Implies(Less(D(1), p),
                Implies(Less(D(1), q),
                    Implies(NotEqual(p, q),
                        Equal(Call("minimumSize", new Formula.SetLiteral([p, q])), D(5)))))));
        return Disp(IffFormula(F.Id("claim"), quantified));
    }

    private static Formula ResultFormula() =>
        Disp(new Formula.Not(F.Id("claim")));

    private static Formula ForAll(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(variable), domain, body);

    private static Formula Exists(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists,
            FormulaIdentifier.Create(variable), domain, body);

    private static Formula Finset(Formula carrier) => Call("Finset", carrier);

    private static Formula SetOf(Formula carrier) => Call("Set", carrier);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula ComplexNumbers() => Seq(Mathbb, Grp(F.Id("C")));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula IffFormula(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));

    private static Formula Implies(Formula hypothesis, Formula conclusion) =>
        new Formula.Logic(
            Parenthesized(hypothesis), FormulaLogicOperator.Implies,
            Parenthesized(conclusion));

    private static Formula Conjoin(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = And(clauses[i], result);
        return result;
    }

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
