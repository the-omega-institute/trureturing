using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class A025529PrimeCubeRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithSums/A025529PrimeCubeRefutation.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/eldar2019a025529");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The prime cube 16843^3 refutes the composite-solution classification for A025529.",
        H("A025529: a prime-cube counterexample"),
        Blocks(
            Node("A", "The LCM-weighted harmonic sum", SequenceFormula(),
                "Let L(m) be the least common multiple of 1 through m. Define A(m) as "
                    + "the sum of the exact natural quotients L(m)/k for 1<=k<=m. "
                    + "Under the rational embedding this is L(m) times harmonic(m), "
                    + "as proved inside the lifting argument. The conventions are "
                    + "L(0)=1, harmonic(0)=0 and A(0)=0.", DescribeRole.Definition),
            Node("PrimeSquareOnly", "The composite-solution predicate", ClaimFormula(),
                "PrimeSquareOnly is the formal encoding of the composite-solution "
                    + "conjecture in the 2019 comment on OEIS A025529: every composite n "
                    + "with n dividing A(n-1) is the square of a prime greater than three. "
                    + "The conjunction 1<n and not Prime(n) expresses compositeness.",
                DescribeRole.Definition),
            Node("prime_cube_divides", "Lifting a short harmonic congruence", LiftingFormula(),
                "For a prime p>3, work in the subring of rationals whose reduced "
                    + "denominators are not divisible by p. Write U(N) for the reciprocal "
                    + "sum over 1<=k<N with p not dividing k. Reflection k maps to N-k "
                    + "proves U(N)/N belongs to this subring whenever p divides N. "
                    + "Partitioning denominators gives p^2 H(p^3-1)=H(p-1)+p U(p^2)"
                    + "+p^2 U(p^3). The short ring congruence implies H(p-1)/p^3 "
                    + "belongs to the subring, by clearing the unit denominator (p-1)! "
                    + "abstractly. Since p^2 divides L(p^3-1), the rational identity "
                    + "for A transfers this to the asserted integer divisibility. "
                    + "The ring ZMod(p^3) is not treated as a field: every required "
                    + "denominator is proved to be a unit.", DescribeRole.Theorem),
            Node("prime_square_only_refuted", "The complete classification is false",
                F.Disp(new Formula.Not(F.Id("PrimeSquareOnly"))),
                "The proof establishes that 16843 is prime and checks all 16842 "
                    + "reciprocal terms modulo 16843^3, obtaining zero. The lifting "
                    + "theorem then proves 4778134229107 divides A(4778134229106). "
                    + "This integer equals 16843^3, is composite, and cannot equal the "
                    + "square of any prime. The finite computation occurs in the proof "
                    + "of the negation. Neither the trillion-term harmonic sum nor the "
                    + "large LCM is evaluated. No exact valuation-three assertion or "
                    + "all-exponent valuation identity is used.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula statement,
        string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create("a025529-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(statement),
            name is "A" or "PrimeSquareOnly"
                ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula SequenceFormula()
    {
        var m = F.Id("m");
        var k = F.Id("k");
        var sum = F.Seq(F.Sum, F.Underscore, F.Grp(Equal(k, F.D(1))), F.Caret, F.Grp(m),
            new Formula.Fraction(Call("lcmUpto", m), k));
        return F.Disp(Universal("m", Equal(Call("A", m), sum)));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n");
        var q = F.Id("q");
        var premise = And(Less(F.D(1), n), new Formula.Not(Call("Prime", n)),
            Divides(n, Call("A", Subtract(n, F.D(1)))));
        var conclusion = new Formula.Bind(FormulaQuantifier.Exists,
            FormulaIdentifier.Create("q"), Naturals(),
            And(Call("Prime", q), Less(F.D(3), q), Equal(n, Power(q, 2))));
        return F.Disp(new Formula.Logic(F.Id("PrimeSquareOnly"),
            FormulaLogicOperator.Iff, Parens(Universal("n", Implies(premise, conclusion)))));
    }

    private static Formula LiftingFormula()
    {
        var p = F.Id("p");
        var k = F.Id("k");
        var sum = F.Seq(F.Sum, F.Underscore, F.Grp(Equal(k, F.D(1))), F.Caret,
            F.Grp(Subtract(p, F.D(1))), new Formula.Power(k, F.Seq(F.Minus, F.D(1))));
        var residue = Equal(new Formula.Modulo(sum, Power(p, 3)), F.D(0));
        return F.Disp(Universal("p", Implies(
            And(Call("Prime", p), Less(F.D(3), p), residue),
            Divides(Power(p, 3), Call("A", Subtract(Power(p, 3), F.D(1)))))));
    }

    private static Formula Universal(string variable, Formula body) => new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), Naturals(), body);
    private static Formula Naturals() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Power(Formula value, byte exponent) => new Formula.Power(value, F.D(exponent));
    private static Formula Parens(Formula value) => F.Seq(F.Open, value, F.Close);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parens(left), FormulaLogicOperator.Implies, Parens(right));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Divides(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Divides, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula And(params Formula[] clauses)
    {
        Formula result = Parens(clauses[^1]);
        for (int i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(Parens(clauses[i]), FormulaLogicOperator.And, result);
        return result;
    }
}
