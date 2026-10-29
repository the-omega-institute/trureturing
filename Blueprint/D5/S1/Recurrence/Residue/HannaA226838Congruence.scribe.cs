using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class HannaA226838CongruenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Residue/HannaA226838Congruence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/hanna2013a226838");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every factorial-normalized coefficient of the original square-exponent rational EGF has an integral residue witness modulo six.",
        H("Hanna's A226838 congruence"),
        Blocks(
            Paragraph(Text("All series are formal power series over the rationals. The notation natval "
                + "denotes the natural-to-rational cast, val the integer-to-rational cast, and coeff(n,f) "
                + "the ordinary coefficient of degree n. The source is exp(sum over m>=1 of X^(m^2)/m^m): "
                + "the exponent is a square and the denominator is a power, not a factorial. "
                + "Natural division in innerIntegral is expressed by a floor. No analytic convergence "
                + "or integrality hypothesis is imposed.")),
            Node("H", "The literal inner series",
                Disp(Eqn(Named("H"), App(Qualified("PowerSeries", "mk"),
                    Seq(F.Id("n"), Mapsto, Sp, Call("finsum",
                        Seq(Par(Seq(F.Id("m"), Colon, Naturals())), Mapsto, Sp,
                            Call("ite", Rel(D(0), FormulaRelationOperator.LessThan, F.Id("m")),
                                Call("coeff", F.Id("n"), Call("monomial", Square(F.Id("m")),
                                    new Formula.Fraction(D(1), Pow(Call("natval", F.Id("m")), F.Id("m"))))),
                                D(0)))))))),
                "This is the coefficientwise finsum over every natural m with the guard 0<m. "
                + "For each degree n, coeff_H bounds its support by m<=n using le_square. "
                + "Thus this definition represents the original unbounded positive-index formal sum, "
                + "rather than a truncated generating function.", DescribeRole.Definition),
            Node("A", "The formal exponential",
                Disp(Eqn(Named("A"), App(Qualified("PowerSeries", "subst"),
                    App(Qualified("PowerSeries", "exp"), Rationals()), Named("H")))),
                "The argument order is subst(exp(Q),H), namely substitution of H into exp(Q). "
                + "The private H_zero supplies constantCoeff(H)=0 before eCoeff_composition is applied.",
                DescribeRole.Definition),
            Node("innerIntegral", "The derived natural inner coefficients",
                Disp(Seq(Bound("n", Naturals()), Eqn(Call("innerIntegral", F.Id("n")),
                    Seq(Sum, Underscore, Grp(Seq(F.Id("m"), Eq, D(0))), Caret, Grp(F.Id("n")), Sp,
                        Call("ite", new Formula.Logic(
                            Rel(D(0), FormulaRelationOperator.LessThan, F.Id("m")),
                            FormulaLogicOperator.And, Eqn(Square(F.Id("m")), F.Id("n"))),
                            new Formula.Floor(new Formula.Fraction(Fact(F.Id("n")), Pow(F.Id("m"), F.Id("m")))),
                            D(0)))))),
                "The sum is over range(n+1), hence m=0 through n inclusive; all division here is in Nat. "
                + "At m>0 and m^2=n, power_dvd_square_factorial gives m^m dividing n!. "
                + "factorial_ratio uses that divisibility and a nonzero rational denominator to identify "
                + "the quotient cast with n!/(m:Q)^m. Then eCoeff_H proves that innerIntegral(n), "
                + "cast to Q, equals n! times coeff(n,H). Integrality is derived, not assumed.",
                DescribeRole.Definition),
            Node("result", "The congruence for every natural index",
                Disp(Seq(Bound("n", Naturals()), Exists, Sp, F.Id("k"), Colon, Integers(), Comma, Sp,
                    Eqn(Mul(Call("natval", Fact(F.Id("n"))), Call("coeff", F.Id("n"), Named("A"))),
                        Add(D(1), Mul(D(6), Call("val", F.Id("k"))))))),
                "OEIS A226838 revision #14 states: a(n) == 1 (mod 6) (conjecture - valid up to "
                + "n=1024; if true for n>=0, why?). The existential integer witness proves integrality "
                + "and the residue simultaneously for every n, including zero. For m>=2, "
                + "six_power_dvd_square_factorial proves 6*m^m divides (m^2)!, treating m=2 and m=3 "
                + "directly and using product-factorial divisibility for larger m. inner_mod_six "
                + "therefore reduces the integral inner coefficient sequence to the identity sequence. "
                + "The result uses eCoeff_H, H_zero, inner_mod_six and composition_unit_mod_six. "
                + "The existing IntegralEGFComposition.eCoeff_composition, eCoeff_exp and composition_map, "
                + "together with the original private QuarticEGFModFour.composition_identity_right, "
                + "transfer that identity through the integral composition law. The private "
                + "BourasA363347PrimeMultiplicity.pow_dvd_factorial_mul supplies the factorial divisibility. "
                + "Only integers are reduced to ZMod(6); there is no rational-to-residue-ring map. "
                + "The theorem and its nine consumed private helpers are conservatively classified "
                + "bind-only under the external named open-problem exception; H, A and innerIntegral "
                + "are definitions earned by result. This is an unbounded symbolic argument, not a "
                + "bounded enumeration or a certified finite instance, so utility is none. "
                + "The proof is repository-derived and is not attributed to OEIS. Bounded literature "
                + "clearance certifies no global novelty. An independent focused reading of Yuta Nishibuchi, "
                + "A Unified Framework for p-adic Congruences and p-adic Interpolations of Sequences, "
                + "arXiv:2610.11648v2 (history https://arxiv.org/abs/2610.11648, v2 abstract "
                + "https://arxiv.org/abs/2610.11648v2, HTML https://arxiv.org/html/2610.11648v2, "
                + "PDF https://arxiv.org/pdf/2610.11648v2, source archive https://arxiv.org/src/2610.11648v2) "
                + "established no exact implication for this series in that source. The paper supplies "
                + "conditional p-adic criteria, but applying them here would require target-specific "
                + "normalized coefficient valuations or a valid decomposition, the correct period, prime "
                + "strength, and base-value links for both p=2 and p=3, all-index coverage including zero, "
                + "and a global integrality bridge to an integer witness. These conditions remain unverified "
                + "for this series. This reading does not claim that the conditions are false or rule out "
                + "the method, and it does not establish a global novelty or priority claim. The paper is "
                + "prior-work context, not the identifier of the OEIS source and not an asserted proof of "
                + "this conjecture.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role) => Describe.Lean(
        DescribeId.Create("hanna-a226838-" + (name == "A" ? "outer" : name == "H" ? "inner" : name.ToLowerInvariant())),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula App(Formula f, params Formula[] xs) => new Formula.Apply(f, [.. xs]);
    private static Formula Call(string name, params Formula[] xs) => App(Named(name), xs);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Fact(Formula f) => Seq(f, Bang);
    private static Formula Pow(Formula f, Formula e) => new Formula.Power(f, e);
    private static Formula Square(Formula f) => Pow(f, D(2));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Bound(string name, Formula type) => Seq(Forall, Sp, F.Id(name), Colon, type, Comma, Sp);
    private static Formula Eqn(Formula x, Formula y) => Rel(x, FormulaRelationOperator.Equal, y);
    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) => new Formula.Relation(x, op, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
}
