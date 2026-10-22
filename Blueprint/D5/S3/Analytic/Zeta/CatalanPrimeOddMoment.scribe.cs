using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Zeta;

internal sealed class CatalanPrimeOddMomentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Zeta/CatalanPrimeOddMoment.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ArithUnits/yaoxu2026catalanmoment");
    private static readonly Formula t = F.Id("t"), p = F.Id("p"), a = F.Id("a");
    private static Formula Chi => F.Id("c");
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Call(string name, Formula x) =>
        Seq(Operatorname, Grp(F.Id(name)), Open, x, Close);
    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, x, Colon, type, Close, Comma, Sp, body);
    private static Formula Char => Seq(Operatorname, Grp(F.Id("DirichletCharacter")),
        Open, Complex, Comma, p, Close);
    private static Formula Sum => Seq(F.Sum, Underscore, Grp(a, Colon, Call("ZMod", p)),
        Sp, Call("val", a), Sp, Chi, Open, a, Close);
    private static Formula PrimeBody(Formula body) => All(p, Nat,
        Seq(OpenBracket, Call("Prime", p), CloseBracket, Sp, All(Chi, Char,
            Seq(Chi, Neq, D(1), Sp, Rightarrow, Sp, body))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The boundary logarithm series evaluates the Hurwitz zeta function at zero. "
            + "The resulting finite L-value identity and the functional equation give prime odd-character nonvanishing.",
        H("Prime Odd-Character Weighted Moments"),
        Blocks(
            Paragraph(Text("The results below follow the immutable eight-module CharacterSpecialValue "
                + "closure of Yao Xu's catalan-lean4 source. They concern complex Dirichlet characters, "
                + "with ZMod.val as the natural representative. The prime hypothesis is retained in "
                + "both character statements; no composite induced-character formula follows from it. "
                + "A real Hurwitz argument is first mapped to the unit additive circle. "
                + "In the displayed formulas c denotes the source character χ.")),
            Node("hurwitz", "The Hurwitz zero value on the open unit interval",
                "hurwitzZeta_apply_zero_of_mem_Ioo", All(t, Real,
                    Seq(D(0), Lt, t, Sp, Land, Sp, t, Lt, D(1), Sp, Rightarrow, Sp,
                        Call("hurwitzZeta", Call("toUnitAddCircle", t)), Open, D(0), Close, Eq,
                        Frac, Grp(D(1)), Grp(D(2)), Minus, t)),
                "A uniform Dirichlet tail bound permits passage to the boundary value at one. "
                    + "Abel's theorem identifies the exponential series with the negative logarithm. "
                    + "Pairing the arguments t and one minus t gives the sine value, and the odd "
                    + "Hurwitz functional equation gives the displayed value at zero. "
                    + "Here toUnitAddCircle is the canonical map from the real numbers to R/Z; "
                    + "the right side is coerced to the complex numbers."),
            Node("lvalue", "The exact prime weighted representative formula",
                "LFunction_zero_eq_neg_weighted_sum", PrimeBody(
                    Seq(F.Id("L"), Open, D(0), Comma, Chi, Close, Eq, Minus,
                        Frac, Grp(Sum), Grp(p))),
                "Expand the Dirichlet L-function as a finite sum of Hurwitz values. The term at "
                    + "zero vanishes, the other representatives lie in the open unit interval after "
                    + "division by p, and the complete sum of a nonprincipal character is zero."),
            Node("nonvanishing", "The full prime nonprincipal odd-character theorem",
                "odd_character_weighted_sum_ne_zero", PrimeBody(
                    Seq(Chi, Open, Minus, D(1), Close, Eq, Minus, D(1), Sp, Rightarrow, Sp,
                        Sum, Neq, D(0))),
                "A nonprincipal character at prime level is primitive. Nonvanishing of the inverse "
                    + "character's L-value at one and the primitive functional equation force a "
                    + "nonzero completed value at zero. Oddness makes the gamma factor at zero equal "
                    + "to one. The finite weighted-sum identity then proves nonvanishing."),
            Helper("phase-norm", "exp_two_pi_norm",
                "For every real t, the norm of exp(2 pi I t) is one."),
            Helper("phase-not-one", "exp_two_pi_ne_one",
                "For real t strictly between zero and one, exp(2 pi I t) is not one. "
                    + "The exponential equality criterion would otherwise put an integer strictly between zero and one."),
            Helper("phase-powers", "exp_two_pi_pow",
                "For every real t and natural n, the nth power of exp(2 pi I t) equals exp(2 pi I t n), "
                    + "with the indicated real and natural values coerced to the complex numbers."),
            Helper("uniform-tail", "unit_circle_dirichlet_tail_bound",
                "For complex z of norm one with z not equal to one, every real s at least one and "
                    + "natural M and N with one at most M at most N, the norm of the sum of z^n/n^s "
                    + "over M at most n less than N is at most 4/(M times norm(1-z)). The power n^s "
                    + "is complex power at the coerced real exponent. The empty interval M = N remains in scope."),
            Helper("circle-functional-equation", "hurwitzZeta_zero_eq_sinZeta_one_div_pi",
                "For every nonzero a in the unit additive circle, hurwitzZeta(a,0) equals sinZeta(a,1)/pi."),
            Helper("interval-functional-equation", "hurwitzZeta_zero_eq_sine_value_of_mem_Ioo",
                "For every real t strictly between zero and one, the same functional-equation identity "
                    + "holds at the canonical unit-circle image of t."),
            Helper("log-cauchy", "cauchySeq_unit_circle_log_partial_sums",
                "For every complex z of norm one with z not equal to one, the partial sums over "
                    + "n less than N of z^(n+1)/(n+1) form a Cauchy sequence in the complex numbers."),
            Helper("log-limit", "tendsto_unit_circle_log_partial_sums",
                "For every complex z of norm one with z not equal to one, the partial sums over "
                    + "n less than N of z^n/n tend, as N tends to infinity, to -log(1-z). "
                    + "The n = 0 summand uses Lean's division-by-zero convention and is zero."),
            Helper("conditional-boundary", "tendsto_expZeta_one_partial_sums_of_tail_bound",
                "Assuming the complete uniform tail-bound family stated above, for every real t "
                    + "strictly between zero and one the partial sums of exp(2 pi I t n)/n tend to "
                    + "expZeta(toUnitAddCircle(t),1). The assumption quantifies over all z, s, M and N "
                    + "in the tail-bound statement; it is not a bound at a single chosen phase."),
            Helper("argument", "arg_one_sub_exp_two_pi",
                "For every real t strictly between zero and one, arg(1-exp(2 pi I t)) equals pi t - pi/2, "
                    + "using the principal complex argument."),
            Helper("log-difference", "log_one_sub_exp_two_pi_difference",
                "For every real t strictly between zero and one, -log(1-exp(2 pi I t)) plus "
                    + "log(1-exp(2 pi I (1-t))) equals 2 I pi (1/2-t). Both logarithms use the "
                    + "same principal branch; the reflected argument is exactly one minus t."),
            Helper("lzero-nonvanishing", "LFunction_zero_ne_zero_of_prime_odd",
                "For every prime p and every nonprincipal odd complex Dirichlet character modulo p, "
                    + "its Dirichlet L-function at zero is nonzero."),
            Helper("conditional-lzero", "LFunction_zero_eq_neg_weighted_sum_of_hurwitz_zero",
                "Assuming hurwitzZeta(toUnitAddCircle(t),0) = 1/2-t for every real t strictly between "
                    + "zero and one, every prime p and every nonprincipal complex Dirichlet character "
                    + "modulo p satisfy the negative weighted representative-sum formula displayed above. "
                    + "Oddness is not required for this equality."),
            Helper("boundary", "tendsto_expZeta_one_partial_sums",
                "For every real t strictly between zero and one, the partial sums of exp(2 pi I t n)/n "
                    + "tend to expZeta(toUnitAddCircle(t),1). This version supplies the proved uniform "
                    + "tail bound, so it has no tail-bound assumption."),
            Helper("expzeta-log", "expZeta_one_eq_neg_log",
                "For every real t strictly between zero and one, expZeta(toUnitAddCircle(t),1) "
                    + "equals -log(1-exp(2 pi I t))."),
            Helper("sine-value", "sinZeta_one_eq_of_mem_Ioo",
                "For every real t strictly between zero and one, sinZeta(toUnitAddCircle(t),1) "
                    + "equals pi times (1/2-t), with real values coerced to the complex numbers."))));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula statement, string prose) => Describe.Lean(
            DescribeId.Create("catalan-prime-moment-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static DocumentBlock Helper(string id, string declaration, string prose) => Describe.Remark(
        DescribeId.Create("catalan-prime-moment-helper-" + id),
        DeclarationHandle.Create(Prefix + declaration), H(declaration),
        AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))));
}
