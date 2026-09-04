using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms;

internal sealed class PrimaryPseudoperfectPortsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/PrimeForms/PrimaryPseudoperfectPorts.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Primary pseudoperfect numbers admit equivalent reciprocal and integral forms, "
            + "a coprime Leibniz rule, a compositional port residual, and explicit companions.",
        H("Primary Pseudoperfect Ports"),
        Blocks(
            Paragraph(Text(
                "For a natural number n, squarefreeDeriv(n) is the sum of n/p over its "
                    + "prime factors, IsPPN(n) means that n is squarefree, exceeds one, "
                    + "and equals 1 + squarefreeDeriv(n), and portDelta(R,c,B) is the "
                    + "natural-number difference cB - R squarefreeDeriv(B).")),
            Describe.Lean(
                DescribeId.Create("reciprocal-and-integral-characterizations"),
                DeclarationHandle.Create(Prefix + "reciprocal_eq_one_and_isPPN_iff"),
                H("Reciprocal and integral characterizations"),
                StatementSource.FromAuthor(ReciprocalCharacterizations()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For nonzero n, multiplication by n converts the prime-factor "
                        + "reciprocal sum into squarefreeDeriv(n). The same equivalence, "
                        + "combined with squarefreeness and n > 1, characterizes IsPPN."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coprime-leibniz-rule"),
                DeclarationHandle.Create(Prefix + "squarefreeDeriv_mul"),
                H("Coprime Leibniz rule"),
                StatementSource.FromAuthor(LeibnizRule()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Coprimality partitions the prime factors of AB into disjoint factors "
                        + "from A and B. Transporting complementary divisors across that "
                        + "partition gives the two Leibniz terms."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("port-composition-law"),
                DeclarationHandle.Create(Prefix + "portDelta_mul"),
                H("Port composition law"),
                StatementSource.FromAuthor(PortComposition()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On coprime factors, the Leibniz rule makes the residual through AB "
                        + "equal to the residual obtained by substituting the output at A "
                        + "as the input coefficient at B."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coprime-extension-criterion"),
                DeclarationHandle.Create(Prefix + "isPPN_mul_iff_port"),
                H("Coprime extension criterion"),
                StatementSource.FromAuthor(CoprimeExtension()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If K is primary pseudoperfect and C is a nontrivial squarefree factor "
                        + "coprime to K, then KC is primary pseudoperfect exactly when the "
                        + "natural residual C - K squarefreeDeriv(C) equals one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("companions-and-numeric-chain"),
                DeclarationHandle.Create(Prefix + "isPPN_companions"),
                H("One-prime and two-prime companions and the numeric chain"),
                StatementSource.FromAuthor(Companions()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The bundled statement records the Euclid-style K(K+1) step, the "
                        + "two-prime factored port criterion in the K < p,q natural-number "
                        + "domain, and the checked chain 2, 6, 42, 1806, 47058."))),
                DescribeRole.Theorem))));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Reciprocal(Formula value) =>
        Seq(Frac, Grp(D(1)), Grp(value));

    private static Formula Deriv(Formula value) => Call("squarefreeDeriv", value);

    private static Formula Ppn(Formula value) => Call("IsPPN", value);

    private static Formula Prime(Formula value) => Call("Prime", value);

    private static Formula Squarefree(Formula value) => Call("Squarefree", value);

    private static Formula Coprime(Formula left, Formula right) =>
        Call("Coprime", left, right);

    private static Formula PowerTwo(Formula value) => Seq(Grp(value), Caret, D(2));

    private static Formula IffFormula(Formula left, Formula right) =>
        Seq(Open, left, Sp, Iff, Sp, right, Close);

    private static Formula AndFormula(params Formula[] clauses)
    {
        var items = new List<Formula>();
        for (var i = 0; i < clauses.Length; i++)
        {
            if (i > 0) items.AddRange([Sp, Land, Sp]);
            items.Add(clauses[i]);
        }
        return Seq([.. items]);
    }

    private static Formula PrimeFactorReciprocalSum(Formula n)
    {
        Formula p = F.Id("p");
        return Seq(
            Sum, Underscore,
            Grp(p, Sp, InMacro, Sp, Call("primeFactors", n)), Sp,
            Reciprocal(p));
    }

    private static Formula ReciprocalEquation(Formula n) =>
        Equal(Add(Reciprocal(n), PrimeFactorReciprocalSum(n)), Num(1));

    private static Formula ReciprocalCharacterizations()
    {
        Formula n = F.Id("n");
        Formula nonzeroEquivalence = Seq(
            n, Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp,
            IffFormula(ReciprocalEquation(n), Equal(n, Add(Num(1), Deriv(n)))));
        Formula ppnEquivalence = IffFormula(
            Ppn(n),
            AndFormula(Squarefree(n), Seq(D(1), Sp, Lt, Sp, n), ReciprocalEquation(n)));
        return Disp(Seq(
            Forall, Sp, n, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            Grp(nonzeroEquivalence), Sp, Land, Sp, Grp(ppnEquivalence), Dot));
    }

    private static Formula LeibnizRule()
    {
        Formula a = F.Id("A");
        Formula b = F.Id("B");
        return Disp(Seq(
            Forall, Sp, a, Comma, Sp, b, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            Coprime(a, b), Sp, Rightarrow, Sp,
            Equal(
                Deriv(Multiply(a, b)),
                Add(Multiply(a, Deriv(b)), Multiply(b, Deriv(a)))), Dot));
    }

    private static Formula PortComposition()
    {
        Formula a = F.Id("A");
        Formula b = F.Id("B");
        Formula r = F.Id("R");
        Formula c = F.Id("c");
        return Disp(Seq(
            Forall, Sp, a, Comma, Sp, b, Comma, Sp, r, Comma, Sp, c,
            Sp, InMacro, Sp, Naturals(), Comma, Sp,
            Coprime(a, b), Sp, Rightarrow, Sp,
            Equal(
                Call("portDelta", r, c, Multiply(a, b)),
                Call("portDelta", Multiply(r, a), Call("portDelta", r, c, a), b)), Dot));
    }

    private static Formula CoprimeExtension()
    {
        Formula k = F.Id("K");
        Formula c = F.Id("C");
        Formula hypotheses = AndFormula(
            Ppn(k), Squarefree(c), Seq(D(1), Sp, Lt, Sp, c), Coprime(k, c));
        Formula conclusion = IffFormula(
            Ppn(Multiply(k, c)),
            Equal(Subtract(c, Multiply(k, Deriv(c))), Num(1)));
        return Disp(Seq(
            Forall, Sp, k, Comma, Sp, c, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            hypotheses, Sp, Rightarrow, Sp, conclusion, Dot));
    }

    private static Formula NotDivides(Formula left, Formula right) =>
        Seq(Neg, Sp, Grp(left, Sp, Mid, Sp, right));

    private static Formula Companions()
    {
        Formula k = F.Id("K");
        Formula p = F.Id("p");
        Formula q = F.Id("q");
        Formula successor = Add(k, Num(1));
        Formula onePrime = Seq(
            Forall, Sp, k, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            AndFormula(Ppn(k), Prime(successor)), Sp, Rightarrow, Sp,
            Ppn(Multiply(k, successor)));
        Formula twoPrimeHypotheses = AndFormula(
            Ppn(k), Prime(p), Prime(q), Seq(p, Sp, Neq, Sp, q),
            NotDivides(p, k), NotDivides(q, k),
            Seq(k, Sp, Lt, Sp, p), Seq(k, Sp, Lt, Sp, q));
        Formula twoPrime = Seq(
            Forall, Sp, k, Comma, Sp, p, Comma, Sp, q,
            Sp, InMacro, Sp, Naturals(), Comma, Sp,
            twoPrimeHypotheses, Sp, Rightarrow, Sp,
            IffFormula(
                Ppn(Multiply(Multiply(k, p), q)),
                Equal(
                    Multiply(Subtract(p, k), Subtract(q, k)),
                    Add(PowerTwo(k), Num(1)))));
        Formula numericChain = AndFormula(
            Ppn(Num(2)), Ppn(Num(6)), Ppn(Num(42)), Ppn(Num(1806)), Ppn(Num(47058)));
        return Disp(Seq(
            Grp(onePrime), Sp, Land, Sp,
            Grp(twoPrime), Sp, Land, Sp,
            Grp(numericChain), Dot));
    }
}
