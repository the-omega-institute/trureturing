using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Decoherence;

internal sealed class EntanglementBufferAvailabilityLowerBoundDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Decoherence/EntanglementBufferAvailabilityLowerBound";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/QuantumContext/inestaetal2026entanglementbuffering");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The always-failing purification policy at q equal to one attains the minimum buffer availability.",
        H("A sharp lower bound for entanglement-buffer availability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("admissible"),
                DeclarationHandle.Create(Module + ".admissible"),
                H("Admissible purification coefficients"),
                StatementSource.FromAuthor(Disp(AdmissibleFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For each k in Fin n, the success probability c(k)(f − 1/4) + d(k) lies between zero and one "
                    + "for every input fidelity f between 1/4 and one. The unnormalized excess fidelity "
                    + "a(k)(f − 1/4) + b(k) lies between zero and three quarters of that probability. "
                    + "These are the probability and output-fidelity conditions of Appendix C, main.tex lines 1735–1757. "
                    + "The index k represents k.val + 1 newly generated links, so Fin n represents the source's indices one through n. "
                    + "The inequalities also include protocols with zero success probability."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("availability"),
                DeclarationHandle.Create(Module + ".availability"),
                H("The closed-form availability"),
                StatementSource.FromAuthor(Disp(AvailabilityFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The expression is the availability formula of Theorem 1, main.tex lines 378–409. "
                    + "Here pg is the generation probability per short-lived memory, pc is the consumption probability, "
                    + "q is the purification probability, gam is the decay parameter, and fnew is the newly generated fidelity. "
                    + "The auxiliary values ta, tb, tc and td are the four normalized, binomially weighted coefficient sums. "
                    + "The weight binomialMass pg n (k.val + 1) is "
                    + "(↑(n.choose (k.val + 1)) : ℝ) · pg^(k.val + 1) · (1 − pg)^(n − (k.val + 1)); "
                    + "the upward arrow includes the natural binomial coefficient in the real numbers. "
                    + "The values tgen and tocc are the expected empty and occupied durations in the source's model. "
                    + "The definition is a real-valued expression for all parameters, with real division defined even at zero; "
                    + "the comparison below imposes the parameter conditions that make the relevant denominators positive. "
                    + "The source identifies this expression with the limiting fraction of consumption requests that find a link, "
                    + "defined at main.tex lines 344–350."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("Comparison with the always-failing policy"),
                StatementSource.FromAuthor(Disp(Equivalence(Local("claim"), ClaimBody()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Fix a positive number n of generation memories, pg and pc in (0,1], gam at least zero, "
                    + "and fnew in (1/4,1]. Every admissible coefficient family and every q in [0,1] has availability "
                    + "at least that of the zero coefficient families at q equal to one. "
                    + "This is the formula-based reading of the conjecture at main.tex lines 500–502. "
                    + "When c and d vanish, admissibility at fidelities 1/4 and one forces b and then a to vanish, "
                    + "so the four zero families describe the always-failing policy."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("The always-failing policy attains the lower bound"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "First set g = 1 − (1 − pg)^n. The binomial expansion shows that the weights "
                        + "binomialMass pg n (k.val + 1), summed over Fin n, have total g. "
                        + "Since n is positive and 0 < pg ≤ 1, one has 0 < g ≤ 1, and every weight is nonnegative.")),
                    Paragraph(Text(
                        "Let aa, bb, cc and dd be the weighted sums of a, b, c and d with these weights. "
                        + "Multiply each admissibility inequality by its nonnegative weight and sum. "
                        + "Evaluating at f = 1/4 and f = 1 gives "
                        + "0 ≤ dd ≤ g, 0 ≤ (3/4)cc + dd ≤ g, 0 ≤ bb ≤ (3/4)dd, and "
                        + "0 ≤ (3/4)aa + bb ≤ (3/4)((3/4)cc + dd).")),
                    Paragraph(Text(
                        "The required estimate for two coordinates uses real u, v, w, z, ell, mu and h with "
                        + "v,w ≥ 0, mu > 0, 0 ≤ h ≤ 1, and both column sums u + w and v + z between ell and 1 − mu. "
                        + "The transpose of I minus the matrix with rows (u,v) and (w,z) has positive diagonal "
                        + "and is strictly diagonally dominant. Its determinant det = (1 − u)(1 − z) − vw is therefore positive. "
                        + "Put y0 = (1 − z)h + v(1 − h) and y1 = wh + (1 − u)(1 − h). "
                        + "Both are nonnegative. The identity "
                        + "(1 − ell)(y0 + y1) − det = (u + w − ell)y0 + (v + z − ell)y1 "
                        + "then gives det ≤ (1 − ell)num, where num = y0 + y1.")),
                    Paragraph(Text(
                        "To apply this estimate to the four aggregate coefficients, temporarily call them a,b,c,d, "
                        + "write mu for pc, and take real g,q,e,h with 0 < g ≤ 1, 0 ≤ q ≤ 1, e ≥ 1 and 0 ≤ h ≤ 3/4. "
                        + "Set t = q(1 − mu), ell = (1 − qg)(1 − mu), p = mu + qg(1 − mu), and r = 1/e. "
                        + "Thus 0 ≤ r ≤ 1, t,ell ≥ 0, p > 0, p = 1 − ell and ell + tg = 1 − mu. "
                        + "Use u = (ell + t(a + (4/3)b))r + t((4/3)b)(1 − r), v = t((4/3)b), "
                        + "w = t(d + (3/4)c − a − (4/3)b)r + (ell + t(d − (4/3)b))(1 − r), "
                        + "and z = ell + t(d − (4/3)b).")),
                    Paragraph(Text(
                        "The aggregate endpoint inequalities give d + (3/4)c − a − (4/3)b ≥ 0 and d − (4/3)b ≥ 0, "
                        + "so v and w are nonnegative. Moreover, "
                        + "u + w = ell + t(r((3/4)c + d) + (1 − r)d) and v + z = ell + td. "
                        + "The convex combination in the first expression, and d in the second, lie in [0,g]. "
                        + "Both column sums therefore lie in [ell,1 − mu]. Apply the two-coordinate estimate "
                        + "with initial first coordinate (4/3)h. For its determinant det and numerator num, "
                        + "direct algebra gives e·det = (e − ell − t·a)(p − t·d) − t²bc and "
                        + "e·num = e − ell − t·a + t·c·h. Thus x = e − ell is positive, "
                        + "D = (x − t·a)(p − t·d) − t²bc is positive, and "
                        + "1 ≤ p((x − t·a + t·c·h)/D).")),
                    Paragraph(Text(
                        "Now take e = Real.exp gam, h = fnew − 1/4 and the weighted coefficients aa,bb,cc,dd. "
                        + "The parameter assumptions give e ≥ 1 and 0 ≤ h ≤ 3/4. "
                        + "Put x = Real.exp gam − (1 − q + q(1 − pg)^n)(1 − pc), "
                        + "p = pc + qg(1 − pc), t = q(1 − pc), "
                        + "det = (x − t·aa)(p − t·dd) − t²bb·cc, "
                        + "num = x − t·aa + t·cc(fnew − 1/4), and s = num/det. "
                        + "The preceding estimate gives x,p,det > 0 and 1 ≤ p·s, hence s > 0. "
                        + "The normalized denominator (1 − t·aa/x)(1 − t·dd/p) − (t·bb/p)(t·cc/x) "
                        + "equals det/(xp) and is positive. Substituting into the occupied-duration formula "
                        + "and cancelling these nonzero denominators identifies tocc with s. "
                        + "Consequently the availability is s/(1/g + s).")),
                    Paragraph(Text(
                        "Since q ≤ 1, p ≤ pc + (1 − pc)g; multiplying by s yields "
                        + "1 ≤ s(pc + (1 − pc)g). Both denominators in "
                        + "g/(pc + (2 − pc)g) ≤ s/(1/g + s) are positive. "
                        + "Cross multiplication, followed by g(1/g + s) = 1 + gs, "
                        + "reduces the comparison to that last inequality. "
                        + "This proves the stated numerical lower bound for every admissible policy.")),
                    Paragraph(Text(
                        "Finally substitute q = 1 and the four zero coefficient families. "
                        + "All four normalized coefficient sums vanish. With p = pc + g(1 − pc) > 0, "
                        + "the availability simplifies to (1/p)/(1/g + 1/p) = g/(g + p) = g/(pc + (2 − pc)g). "
                        + "Replacing the left side of the desired policy comparison by this value "
                        + "and applying the numerical lower bound proves the claim. "
                        + "The zero families are admissible, so they attain the bound."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("inesta-davies-kar-wehner-2026-entanglement-buffer-availability-lower-bound"),
                    ResolutionKind.Proved)))));

    private static Formula AdmissibleFormula()
    {
        Formula success = Add(Multiply(At(X("c"), X("k")), Subtract(X("f"), Quarter())), At(X("d"), X("k")));
        Formula excess = Add(Multiply(At(X("a"), X("k")), Subtract(X("f"), Quarter())), At(X("b"), X("k")));
        Formula inequalities = And(And(LE(D(0), success), LE(success, D(1))),
            And(LE(D(0), excess), LE(excess, Multiply(ThreeQuarters(), success))));
        return All("n", Naturals(), Coefficients(Equivalence(
            LocalCall("admissible", X("a"), X("b"), X("c"), X("d")),
            All("k", FinOf(X("n")), All("f", Reals(),
                Arrow(LE(Quarter(), X("f")), Arrow(LE(X("f"), D(1)), inequalities)))))));
    }

    private static Formula AvailabilityFormula()
    {
        Formula body = Divide(X("tocc"), Add(X("tgen"), X("tocc")));
        body = LetOf("tocc", Divide(Add(Subtract(D(1), X("ta")),
                Multiply(X("tc"), Subtract(X("fnew"), Quarter()))),
            Multiply(Subtract(Multiply(Subtract(D(1), X("ta")), Subtract(D(1), X("td"))),
                Multiply(X("tb"), X("tc"))), X("p"))), body);
        body = LetOf("tgen", Divide(D(1), GenerationProbability()), body);
        body = LetOf("td", NormalizedCoefficient("d", "p"), body);
        body = LetOf("tc", NormalizedCoefficient("c", "x"), body);
        body = LetOf("tb", NormalizedCoefficient("b", "p"), body);
        body = LetOf("ta", NormalizedCoefficient("a", "x"), body);
        body = LetOf("x", Subtract(At(Qualified("Real", "exp"), X("gam")),
            Multiply(Add(Subtract(D(1), X("q")), Multiply(X("q"), NoGenerationProbability())),
                Subtract(D(1), X("pc")))), body);
        body = LetOf("p", Add(X("pc"), Multiply(Multiply(X("q"), GenerationProbability()),
            Subtract(D(1), X("pc")))), body);
        return All("n", Naturals(), All("pg", Reals(), All("pc", Reals(), All("q", Reals(),
            All("gam", Reals(), All("fnew", Reals(), Coefficients(Equal(
                LocalCall("availability", X("n"), X("pg"), X("pc"), X("q"), X("gam"), X("fnew"),
                    X("a"), X("b"), X("c"), X("d")), Parenthesized(body)))))))));
    }

    private static Formula ClaimBody()
    {
        Formula zero = At(Qualified("Function", "const"), FinOf(X("n")), Typed(D(0), Reals()));
        Formula comparison = LE(
            LocalCall("availability", X("n"), X("pg"), X("pc"), D(1), X("gam"), X("fnew"), zero, zero, zero, zero),
            LocalCall("availability", X("n"), X("pg"), X("pc"), X("q"), X("gam"), X("fnew"),
                X("a"), X("b"), X("c"), X("d")));
        Formula policies = Coefficients(Arrow(LocalCall("admissible", X("a"), X("b"), X("c"), X("d")),
            All("q", Reals(), Arrow(LE(D(0), X("q")), Arrow(LE(X("q"), D(1)), comparison)))));
        Formula body = Arrow(LE(X("fnew"), D(1)), policies);
        body = Arrow(LT(Quarter(), X("fnew")), body);
        body = Arrow(LE(D(0), X("gam")), body);
        body = Arrow(LE(X("pc"), D(1)), body);
        body = Arrow(LT(D(0), X("pc")), body);
        body = Arrow(LE(X("pg"), D(1)), body);
        body = Arrow(LT(D(0), X("pg")), body);
        body = All("fnew", Reals(), body);
        body = All("gam", Reals(), body);
        body = All("pc", Reals(), body);
        body = All("pg", Reals(), body);
        return All("n", Naturals(), Arrow(LE(D(1), X("n")), body));
    }

    private static Formula NormalizedCoefficient(string name, string denominator) => Divide(
        Multiply(Multiply(X("q"), Subtract(D(1), X("pc"))),
            At(Qualified("dotProduct"), X(name), LambdaOf("k", FinOf(X("n")),
                At(Qualified("D5", "S3", "AnalyticClosure", "BinomialLocalGaussian", "binomialMass"),
                    X("pg"), X("n"), Add(At(Qualified("Fin", "val"), X("k")), D(1)))))), X(denominator));
    private static Formula NoGenerationProbability() =>
        new Formula.Power(Parenthesized(Subtract(D(1), X("pg"))), X("n"));
    private static Formula GenerationProbability() => Subtract(D(1), NoGenerationProbability());
    private static Formula Coefficients(Formula body) =>
        All("a", Family(), All("b", Family(), All("c", Family(), All("d", Family(), body))));
    private static Formula Family() => new Formula.TypeArrow(FinOf(X("n")), Reals());
    private static Formula Local(string name) =>
        Qualified("D5", "S3", "Quantum", "Decoherence", "EntanglementBufferAvailabilityLowerBound", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula X(string name) => F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula Quarter() => Divide(D(1), D(4));
    private static Formula ThreeQuarters() => Divide(D(3), D(4));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula LetOf(string name, Formula value, Formula body) => Seq(
        Qualified("let"), Sp, Typed(X(name), Reals()), Sp, Colon, Eq, Sp, Parenthesized(value), Semi, Sp, body);
    private static Formula Arrow(Formula premise, Formula conclusion) =>
        new Formula.TypeArrow(Parenthesized(premise), Parenthesized(conclusion));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula LT(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Divide(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
}
