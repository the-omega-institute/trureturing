using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Periodic;

internal sealed class IntegralEgfTotientPeriodDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Periodic/IntegralEgfTotientPeriod.";
    private static readonly LibraryNoteRef SpecificSource =
        LibraryNoteRef.Create("D5/L/ArithSums/bala2022a305550");
    private static readonly LibraryNoteRef GeneralSource =
        LibraryNoteRef.Create("D5/L/ArithSums/bala2022egfgeneral");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral exponential substitutions have totient periods, including OEIS A305550.",
        H("Totient Periods for Integral Exponential Substitutions"),
        Blocks(
            Paragraph(Text("The notes bala2022a305550 and bala2022egfgeneral record Bala's "
                + "specific and broader conjectures. The broader sentence appears on both "
                + "A305550 and A004123 and is one conjecture, settled once. Every positive "
                + "modulus m has period totient(m) from n at least m. Neither the onset "
                + "nor the period is asserted to be minimal.")),
            Paragraph(Text("All indices are natural numbers. The function g maps natural "
                + "numbers to integers. The functions Q, a, egfCoefficient and the imported "
                + "T are integer-valued. Here T(g,n) is the factorial-weighted Stirling "
                + "transform from StirlingTransformTotientPeriod: the sum of "
                + "g(k) times k! times Nat.stirlingSecond(n,k) over k at most n. "
                + "The notation rat denotes the cast to the rationals, integer denotes "
                + "the natural-number cast to the integers, and residue(m,z) denotes "
                + "the integer cast to ZMod m. The function factorial is Nat.factorial "
                + "and totient is Nat.totient.")),
            Paragraph(Text("Every power series here has rational coefficients. The symbols "
                + "X and exp denote PowerSeries.X and PowerSeries.exp over the rationals. "
                + "The function mk forms a power series from its coefficients, coeff(n,F) "
                + "extracts its coefficient at n, and subst(F,H) substitutes H into F. "
                + "The function num returns the numerator of a rational in reduced form "
                + "with positive denominator. Fractions in the generating identity are "
                + "rational division. HasProd(f,F) states convergence of the finite "
                + "products of f to F in the coefficientwise topology; tprod(f) is the "
                + "corresponding infinite product. The function distincts is Mathlib's "
                + "Nat.Partition.distincts, and card is finite-set cardinality.")),
            Node("egf_shift_eq_stirling_transform", "The exponential Stirling bridge",
                BridgeFormula(),
                "Expand each power of exp(X)-1 by the binomial theorem. Powers of exp "
                + "are rescaled exponentials, whose degree-n coefficients are j^n/n!. "
                + "The imported Stirling inclusion-exclusion identity therefore gives "
                + "n! times coeff(n,(exp(X)-1)^k) equal to k! times S(n,k). "
                + "Since exp(X)-1 has zero constant coefficient, its k-th power is "
                + "divisible by X^k. Terms with k greater than n vanish, turning "
                + "substitution into a finite sum and proving the displayed bridge. "
                + "Its integer right-hand side proves integrality as well.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("Q", "Distinct-part partition counts", QFormula(),
                "Q counts partitions into distinct positive parts using Mathlib's "
                + "existing finite set, and casts the count to an integer.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("distinct_parts_generating_identity", "The ordinary partition product",
                PartitionFormula(),
                "Mathlib's count-restricted partition product at multiplicity bound "
                + "two is the distinct-part product. Each factor is 1+X^(j+1).",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("egfCoefficient", "The integer exponential coefficients",
                CoefficientFormula(),
                "The bridge proves the scaled rational coefficient is an integer. "
                + "Taking its reduced numerator therefore extracts that integer "
                + "exactly, and yields T(g,n). Thus egfCoefficient is the coefficient "
                + "sequence of the e.g.f. G(exp(X)-1), for integral G with coefficients g.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("a", "The sequence of OEIS A305550", SequenceFormula(),
                "Use the distinct-part counts Q as the integral coefficients of G. "
                + "The next identity establishes the product e.g.f. at every degree, "
                + "with offset zero.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("generating_equation", "The defining product e.g.f.", GeneratingFormula(),
                "In each degree, substitution is a finite linear combination of "
                + "coefficients and hence is continuous. Applying its algebra "
                + "homomorphism to the ordinary partition product gives the product "
                + "of 1+(exp(X)-1)^(j+1). The coefficient bridge identifies its "
                + "degree-n coefficient with a(n)/n!, giving exactly the e.g.f. "
                + "recorded in bala2022a305550.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("bala_conjecture_egf_general", "Bala's broader e.g.f. conjecture",
                PeriodFormula(true),
                "The bridge identifies egfCoefficient(g,n) with the imported T(g,n). "
                + "The weighted Stirling-transform totient-period theorem gives the "
                + "displayed equality for every integral g and positive m from n "
                + "at least m. This settles the single broader conjecture documented "
                + "in bala2022egfgeneral, including its duplicate occurrence on A004123.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(GeneralSource),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a305550-integral-egf-substitution-totient-period"),
                    ResolutionKind.Proved)),
            Node("bala_conjecture_a305550", "Bala's A305550 conjecture",
                PeriodFormula(false),
                "Specialize the broader theorem to Q. The proved generating_equation "
                + "identifies a with the sequence of the defining A305550 product "
                + "e.g.f., so the equality proves the conjecture in bala2022a305550.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(SpecificSource),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a305550-distinct-part-egf-totient-period"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("integral-egf-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula BridgeFormula() => Disp(Seq(WeightBound(), Sp, Bound("n"), Sp,
        Equality(ScaledCoefficient(), Rat(Call("T", G(), N())))));

    private static Formula QFormula() => Disp(Seq(Bound("n"), Sp,
        Equality(Call("Q", N()), Call("integer", Call("card", Call("distincts", N()))))));

    private static Formula PartitionFormula() => Disp(Call("HasProd",
        Lambda("j", Add(D(1), Power(X(), Add(J(), D(1))))),
        Call("mk", Lambda("k", Rat(Call("Q", K()))))));

    private static Formula CoefficientFormula() => Disp(Seq(WeightBound(), Sp, Bound("n"), Sp,
        Equality(Call("egfCoefficient", G(), N()), Call("num", ScaledCoefficient()))));

    private static Formula SequenceFormula() => Disp(Seq(Bound("n"), Sp,
        Equality(Call("a", N()), Call("egfCoefficient", F.Id("Q"), N()))));

    private static Formula GeneratingFormula() => Disp(Equality(
        Call("mk", Lambda("n", new Formula.Fraction(Rat(Call("a", N())),
            Rat(Call("factorial", N()))))),
        Call("tprod", Lambda("j", Add(D(1), Power(Shift(), Add(J(), D(1))))))));

    private static Formula PeriodFormula(bool general)
    {
        Formula Term(Formula index) => general
            ? Call("egfCoefficient", G(), index) : Call("a", index);
        var equality = Equality(Residue(Term(Add(N(), Call("totient", M())))), Residue(Term(N())));
        var body = Seq(Bound("m", "n"), Sp,
            Implication(Seq(D(0), Sp, Lt, Sp, M()),
                Implication(Seq(M(), Sp, Le, Sp, N()), equality)));
        return Disp(general ? Seq(WeightBound(), Sp, body) : body);
    }

    private static Formula ScaledCoefficient() => Mul(Rat(Call("factorial", N())),
        Call("coeff", N(), Call("subst", Call("mk", Lambda("k", Rat(Call("g", K())))), Shift())));
    private static Formula Shift() => Parenthesized(Subtract(F.Id("exp"), D(1)));
    private static Formula Rat(Formula x) => Call("rat", x);
    private static Formula Residue(Formula x) => Call("residue", M(), x);
    private static Formula G() => F.Id("g");
    private static Formula N() => F.Id("n");
    private static Formula M() => F.Id("m");
    private static Formula K() => F.Id("k");
    private static Formula J() => F.Id("j");
    private static Formula X() => F.Id("X");
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula WeightBound() => Seq(Forall, Sp, G(), Colon, Sp,
        Naturals(), Sp, To, Sp, Integers(), Comma);
    private static Formula Lambda(string variable, Formula body) => Parenthesized(Seq(
        F.Id(variable), Colon, Sp, Naturals(), Sp, Mapsto, Sp, body));
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Equality(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula Implication(Formula x, Formula y) =>
        Seq(Parenthesized(x), Sp, Implies, Sp, Parenthesized(y));
    private static Formula Power(Formula x, Formula y) => new Formula.Power(Parenthesized(x), y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Subtract(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Bound(params string[] names)
    {
        List<Formula> variables = [];
        foreach (var name in names)
        {
            if (variables.Count > 0) variables.AddRange([Comma, Sp]);
            variables.Add(F.Id(name));
        }
        return Seq(Forall, Sp, Seq([.. variables]), Colon, Sp, Naturals(), Comma);
    }
}
