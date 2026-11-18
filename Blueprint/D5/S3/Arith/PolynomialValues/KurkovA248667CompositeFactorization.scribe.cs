using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.PolynomialValues;

internal sealed class KurkovA248667CompositeFactorizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/PolynomialValues/KurkovA248667CompositeFactorization.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/kimberling2014a248667");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every composite term of A248667 is a product of two terms with indices greater than one.",
        H("Kurkov's Composite-Term Factorization Conjecture"),
        Blocks(
            Node("sourcePolynomial", "The unreduced numerator polynomial", PolynomialFormula(),
                "OEIS A248667, COMMENTS paragraph 1 (electronic entry, no page number): "
                + "The polynomial p(n,x) is defined as the numerator when the sum 1 + 1/(n*x + 1) + 1/((n*x + 1)(n*x + 2)) + ... + 1/((n*x + 1)(n*x + 2)...(n*x + n - 1)) is written as a fraction with denominator (n*x + 1)(n*x + 2)...(n*x + n - 1). For more, see A248664. "
                + "The integer polynomial is the sum of the remaining tails after multiplication by that full denominator. "
                + "Finset.range n contains j with 0 <= j < n; Finset.Ico (j+1) n contains i with j+1 <= i < n. "
                + "Empty products are one. Polynomial.C and Polynomial.X are the constant polynomial and indeterminate over the integers. "
                + "The displayed casts of n and i have type Z. At n=0 the sum is empty.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsSourceSequence", "The increasing source sequence", SequenceFormula(),
                "OEIS A248667, NAME: Numbers k for which coefficients of the polynomial p(k,x) defined in Comments are relatively prime. "
                + "The entry has offset 1,2 and states: so that a(1) = 1 and a(2) = 3. "
                + "Polynomial.IsPrimitive expresses coefficient gcd one over Z. The map a : N -> N is strictly increasing and enumerates exactly the positive n with primitive sourcePolynomial n. "
                + "The auxiliary value a(0)=0 lies outside the positive index range.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Kurkov's conjecture", Disp(Equal(V("claim"), ClaimBody())),
                "OEIS A248667, COMMENTS paragraph 3 (electronic entry, no page number): "
                + "Conjecture: any composite term can be represented as a product a(i)*a(j) (i > 1, j > 1) in at least one way. - _Mikhail Kurkov_, Apr 09 2022 "
                + "Composite means greater than one and not Nat.Prime. Both factor indices exceed one; they may be equal. "
                + "The existence clause establishes that the exact increasing source sequence exists, and the factorization holds for every such sequence and every positive index.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Every composite source term factors internally", Disp(ClaimBody()),
                "A prime dividing all coefficients must divide the leading coefficient n^(n-1), hence n. "
                + "Reduction modulo a prime divisor resets the numerator recurrence to the same value at p-1. "
                + "Membership therefore depends only on the prime divisors of n and is preserved by positive divisors. "
                + "Every power of three belongs, so an increasing exact enumeration exists. Its first positive term is one. "
                + "A composite member splits as p*q with p prime and p,q greater than one; both divisors belong and their indices exceed one.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("kurkov-a248667-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula FunctionType() => Seq(N(), Sp, To, Sp, N());
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula App(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula CastZ(Formula value) => Parenthesized(Seq(value, Colon, Sp, Z()));
    private static Formula Primitive(Formula polynomial) =>
        App(Qualified("Polynomial", "IsPrimitive"), polynomial);

    private static Formula PolynomialFormula()
    {
        var n = V("n");
        var j = V("j");
        var i = V("i");
        var term = Parenthesized(Add(
            Multiply(App(Qualified("Polynomial", "C"), CastZ(n)), Qualified("Polynomial", "X")),
            App(Qualified("Polynomial", "C"), CastZ(i))));
        var tail = Seq(Prod, Underscore,
            Grp(Seq(i, Sp, InMacro, Sp, App(Qualified("Finset", "Ico"), Add(j, D(1)), n))),
            Sp, term);
        var sum = Seq(Sum, Underscore,
            Grp(Seq(j, Sp, InMacro, Sp, App(Qualified("Finset", "range"), n))), Sp, tail);
        return Disp(All("n", N(), Equal(Call("sourcePolynomial", n), sum)));
    }

    private static Formula SequenceFormula()
    {
        var a = V("a");
        var n = V("n");
        var k = V("k");
        return Disp(All("a", FunctionType(), Iff(Call("IsSourceSequence", a),
            And(Equal(App(a, D(0)), D(0)), And(Call("StrictMono", a),
                All("n", N(), Iff(
                    Ex("k", N(), And(Less(D(0), k), Equal(App(a, k), n))),
                    And(Less(D(0), n), Primitive(Call("sourcePolynomial", n))))))))));
    }

    private static Formula ClaimBody()
    {
        var a = V("a");
        var k = V("k");
        var i = V("i");
        var j = V("j");
        return And(Ex("a", FunctionType(), Call("IsSourceSequence", a)),
            All("a", FunctionType(), Imp(Call("IsSourceSequence", a),
                All("k", N(), Imp(Less(D(0), k), Imp(Less(D(1), App(a, k)),
                    Imp(new Formula.Not(App(Qualified("Nat", "Prime"), App(a, k))),
                        Ex("i", N(), Ex("j", N(), And(Less(D(1), i),
                            And(Less(D(1), j), Equal(App(a, k),
                                Multiply(App(a, i), App(a, j))))))))))))));
    }
}
