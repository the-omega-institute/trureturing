using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Hilbert;

internal sealed class NymanUnitIntervalMellinDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Hilbert/NymanUnitIntervalMellin.";
    private static Formula C => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula S => F.Id("s");
    private static Formula X => F.Id("x");
    private static Formula Hspace => F.Id("H");
    private static Formula B => Seq(F.Id("B"), Underscore, Grp(D(0)));
    private static Formula ClosedB => Seq(Overline, Grp(B));
    private static Formula Sub(string name, Formula index) => Seq(F.Id(name), Underscore, Grp(index));
    private static Formula ThetaJ => Seq(Theta, Underscore, Grp(F.Id("j")));
    private static Formula App(Formula function, Formula argument) => Seq(function, Open, argument, Close);
    private static Formula Norm(Formula value) => Seq(Vert, Sp, value, Vert);
    private static Formula Sq(Formula value) => Seq(value, Caret, Grp(D(2)));
    private static Formula Div(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Power(Formula s) => Seq(X, Caret, Grp(s, Minus, D(1)));
    private static Formula Fract(Formula theta) => App(Seq(Operatorname, Grp(F.Id("fract"))), Div(theta, X));
    private static Formula Integral(Formula f, Formula s) => Seq(Int, Underscore, Grp(D(0)), Caret,
        Grp(D(1)), f, Power(s), Thin, F.Id("dx"));
    private static Formula L(Formula s) => Sub("L", s);
    private static Formula V(Formula theta) => Sub("v", theta);
    private static Formula K(Formula s) => Sub("k", s);
    private static Formula Denom(Formula s) => Seq(D(2), Re, Sp, s, Minus, D(1));
    private static Formula Root(Formula s) => Seq(Sqrt, Grp(Denom(s)));
    private static Formula HalfPlane(Formula s) => Seq(Div(D(1), D(2)), Lt, Re, Sp, s);
    private static Formula BindS => Seq(Forall, Sp, S, InMacro, Sp, C, Comma, Sp, HalfPlane(S), Rightarrow, Sp);
    private static Formula BindTheta => Seq(Forall, Sp, Theta, InMacro, Sp, R, Comma, Sp);
    private static Formula BindF => Seq(Forall, Sp, F.Id("f"), InMacro, Sp, Hspace, Comma, Sp);
    private static Formula Ae => Seq(Eq, Underscore, Grp(Operatorname, Grp(F.Id("ae"))));
    private static Formula MellinValue(Formula theta, Formula s) => Seq(Div(theta, Seq(s, Minus, D(1))),
        Minus, Div(Seq(theta, Caret, Grp(s), App(Zeta, s)), s));
    private static Formula ZeroCondition => Seq(App(Zeta, Rho), Eq, D(0), Land, Sp,
        HalfPlane(Rho), Lt, D(1));
    private static Formula Distance => Seq(Div(Root(Rho), Norm(Rho)), Le, Sp,
        App(Seq(Operatorname, Grp(F.Id("infDist"))), Seq(D(1), Comma, ClosedB)));
    private static Formula ZeroResults => Seq(Norm(L(Rho)), Eq, Div(D(1), Root(Rho)), Land, Sp,
        App(L(Rho), D(1)), Eq, Div(D(1), Rho), Land, Sp,
        Open, Forall, Sp, F.Id("f"), InMacro, Sp, ClosedB, Comma, Sp,
        App(L(Rho), F.Id("f")), Eq, D(0), Close, Land, Sp, Distance);
    private static Formula E9 => Seq(BindTheta, D(0), Lt, Theta, Le, D(1), Rightarrow, Sp,
        Forall, Sp, S, InMacro, Sp, C, Comma, Sp, D(0), Lt, Re, Sp, S, Lt, D(1), Rightarrow, Sp,
        Integral(Fract(Theta), S), Eq, MellinValue(Theta, S));
    private static Formula E10 => Seq(Forall, Sp, Rho, InMacro, Sp, C, Comma, Sp,
        App(Seq(Operatorname, Grp(F.Id("IsNontrivialZero"))), Rho), Rightarrow, Sp,
        HalfPlane(Rho), Rightarrow, Sp, ZeroResults);

    private static DocumentBlock Theorem(string name, string title, Formula statement, string explanation) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The unit-interval Mellin functional and the constrained Nyman distance obstruction.",
        H("Unit-Interval Mellin Separation"), Blocks(
            Paragraph(Text("Let mu be Lebesgue measure restricted to the open interval (0,1), and let H be the complex Hilbert space Lp(C,2,mu). The target 1 is the class of the constant function one. For every real theta, v_theta is the class of x |-> fract(theta/x), regarded as complex-valued. All almost-everywhere equalities and integrability statements below use mu. Complex powers on positive real bases use the real logarithm.")),
            Paragraph(Math(Disp(Seq(Hspace, Eq, Operatorname, Grp(F.Id("Lp")), Open, C, Comma, D(2), Comma, Mu, Close,
                Comma, Sp, App(V(Theta), X), Ae, Fract(Theta))))),
            Paragraph(Text("B_0 is exactly the set of finite complex sums below. The length n is any natural number, including zero; u ranges over Fin n to C and theta over Fin n to R. Every parameter satisfies zero less than theta_j at most one. The bar denotes closure in the metric of H.")),
            Paragraph(Math(Disp(Seq(F.Id("f"), InMacro, Sp, B, Iff, Sp, Exists, Sp, F.Id("n"), InMacro, Sp,
                Mathbb, Grp(F.Id("N")), Comma, Sp, Exists, Sp, F.Id("u"), Colon, Operatorname,
                Grp(F.Id("Fin")), Open, F.Id("n"), Close, To, C, Comma, Sp,
                Exists, Sp, Theta, Colon, Operatorname, Grp(F.Id("Fin")), Open, F.Id("n"), Close, To, R,
                Comma, Sp, Open, Forall, Sp, F.Id("j"), Comma, D(0), Lt, ThetaJ,
                Le, D(1), Close, Land, Sp, Sum, Underscore, Grp(F.Id("j")), Sub("u", F.Id("j")),
                ThetaJ, Eq, D(0), Land, Sp, F.Id("f"), Eq, Sum, Underscore,
                Grp(F.Id("j")), Sub("u", F.Id("j")), V(ThetaJ))))),
            Theorem("unitTarget_coe_ae", "The constant representative",
                Seq(D(1), Ae, Open, X, Mapsto, Sp, D(1), Close),
                "The Lp target has the constant-one representative almost everywhere."),
            Theorem("source_memLp", "Bounded measurable fractional parts",
                Seq(BindTheta, Operatorname, Grp(F.Id("MemLp")), Open, Open, X, Mapsto, Sp, Fract(Theta),
                    Close, Comma, D(2), Comma, Mu, Close),
                "The fractional part is measurable and lies between zero and one. Finite measure therefore gives MemLp for every real theta, without a positivity restriction."),
            Theorem("source_coe_ae", "The source representative",
                Seq(BindTheta, V(Theta), Ae, Open, X, Mapsto, Sp, Fract(Theta), Close),
                "The source class is represented by the actual fractional-part function."),
            Theorem("finite_sum_coe_ae", "Representatives of finite sums",
                Seq(Forall, Sp, F.Id("n"), Comma, F.Id("u"), Comma, Theta, Comma, Sp,
                    Sum, Underscore, Grp(F.Id("j")), Sub("u", F.Id("j")), V(ThetaJ), Ae,
                    Open, X, Mapsto, Sp, Sum, Underscore, Grp(F.Id("j")), Sub("u", F.Id("j")),
                    Fract(ThetaJ), Close),
                "For every natural length n, every u : Fin n to C, and every theta : Fin n to R, the Lp sum has the displayed function representative. This identity needs no coefficient constraint or parameter bounds."),
            Theorem("zero_mem_B0", "The empty sum", Seq(D(0), InMacro, Sp, B),
                "The sum indexed by Fin zero satisfies the coefficient constraint and is zero."),
            Theorem("closure_B0_nonempty", "Nonempty metric closure", Seq(ClosedB, Neq, Emptyset),
                "The closure contains zero. Its metric infimum distance is therefore the distance to a nonempty set."),
            Paragraph(Text("For real part of s greater than one half, k_s is the Lp class of x to the power conjugate(s) minus one. Define L_s f as the inner product of k_s with f. The inner product is conjugate-linear in its first argument and complex-linear in its second, so L_s is a continuous complex-linear functional.")),
            Paragraph(Math(Disp(Seq(BindS, App(K(S), X), Ae, Power(Seq(Overline, Grp(S))), Comma, Sp,
                App(L(S), F.Id("f")), Eq, Langle, Sp, K(S), Comma, F.Id("f"), Rangle)))),
            Theorem("kernel_memLp", "Square integrability of the Riesz kernel",
                Seq(BindS, Operatorname, Grp(F.Id("MemLp")), Open, Open, X, Mapsto, Sp,
                    Power(Seq(Overline, Grp(S))), Close, Comma, D(2), Comma, Mu, Close),
                "The squared absolute value is x to the power 2 Re(s) minus 2, whose integral is finite precisely in the stated half-plane."),
            Theorem("kernel_coe_ae", "The conjugated kernel representative",
                Seq(BindS, K(S), Ae, Open, X, Mapsto, Sp, Power(Seq(Overline, Grp(S))), Close),
                "The Riesz vector has the stated representative almost everywhere."),
            Theorem("pairing_integrable", "Integrability of the analytic pairing",
                Seq(BindS, BindF, Operatorname, Grp(F.Id("Integrable")), Open,
                    Open, X, Mapsto, Sp, App(F.Id("f"), X), Power(S), Close, Comma, Mu, Close),
                "The L2 inner-product integrability theorem applies to k_s and every f in H. Conjugating the kernel gives the analytic power x to the power s minus one."),
            Theorem("pairing_integrable_representative", "Integrability for any equal representative",
                Seq(BindS, BindF, Forall, Sp, F.Id("g"), Colon, R, To, C, Comma, Sp,
                    F.Id("f"), Ae, F.Id("g"), Rightarrow, Sp, Operatorname, Grp(F.Id("Integrable")),
                    Open, Open, X, Mapsto, Sp, App(F.Id("g"), X), Power(S), Close, Comma, Mu, Close),
                "Every function almost everywhere equal to the Lp representative has an integrable pairing, with no additional measurability hypothesis."),
            Theorem("mellinFunctional_apply", "The actual Mellin integral",
                Seq(BindS, BindF, App(L(S), F.Id("f")), Eq, Integral(App(F.Id("f"), X), S)),
                "The continuous functional equals the literal Lebesgue integral over the open unit interval."),
            Theorem("mellinFunctional_apply_representative", "Independence of representatives",
                Seq(BindS, BindF, Forall, Sp, F.Id("g"), Colon, R, To, C, Comma, Sp,
                    F.Id("f"), Ae, F.Id("g"), Rightarrow, Sp, App(L(S), F.Id("f")), Eq,
                    Integral(App(F.Id("g"), X), S)),
                "Replacing the representative by any almost everywhere equal function leaves the integral unchanged."),
            Theorem("kernel_norm_sq_exact", "Exact squared kernel norm",
                Seq(BindS, Sq(Norm(K(S))), Eq, Div(D(1), Denom(S))),
                "Integrating x to the power 2 Re(s) minus 2 gives the exact squared Hilbert norm."),
            Theorem("mellinFunctional_norm_sq", "Exact squared operator norm",
                Seq(BindS, Sq(Norm(L(S))), Eq, Div(D(1), Denom(S))),
                "The Riesz map is isometric, so the squared operator norm equals the squared kernel norm."),
            Theorem("mellinFunctional_norm", "Exact operator norm",
                Seq(BindS, Norm(L(S)), Eq, Div(D(1), Root(S))),
                "Both sides are nonnegative and their squares agree. The square root is positive in this half-plane."),
            Theorem("mellinFunctional_unitTarget", "Evaluation on the target",
                Seq(BindS, App(L(S), D(1)), Eq, Div(D(1), S)),
                "The unit-interval integral of x to the power s minus one is one over s. The half-plane condition excludes s equal to zero."),
            Theorem("mellinFunctional_source", "Evaluation on every real-parameter source",
                Seq(BindTheta, D(0), Lt, Theta, Le, D(1), Rightarrow, Sp, BindS,
                    Re, Sp, S, Lt, D(1), Rightarrow, Sp, App(L(S), V(Theta)), Eq, MellinValue(Theta, S)),
                "The fractional-part Mellin identity evaluates the actual source for every real theta in (0,1], in the strip one half less than Re(s) less than one."),
            Theorem("mellinFunctional_B0", "Annihilation of constrained finite sums",
                Seq(Forall, Sp, Rho, InMacro, Sp, C, Comma, Sp, ZeroCondition, Rightarrow, Sp,
                    Forall, Sp, F.Id("f"), InMacro, Sp, B, Comma, App(L(Rho), F.Id("f")), Eq, D(0)),
                "At a zero the zeta term vanishes. Complex linearity reduces each finite sum to the coefficient constraint divided by rho minus one."),
            Theorem("mellinFunctional_closure_B0", "Annihilation of the entire closure",
                Seq(Forall, Sp, Rho, InMacro, Sp, C, Comma, Sp, ZeroCondition, Rightarrow, Sp,
                    Forall, Sp, F.Id("f"), InMacro, Sp, ClosedB, Comma, App(L(Rho), F.Id("f")), Eq, D(0)),
                "The kernel of a continuous linear functional is closed, and contains B_0, hence contains its metric closure."),
            Theorem("nyman_unitInterval_zero_obstruction_of_strip", "Distance obstruction in the explicit strip",
                Seq(Forall, Sp, Rho, InMacro, Sp, C, Comma, Sp, ZeroCondition, Rightarrow, Sp, Distance),
                "For every f in the closure, the operator norm bounds the absolute value of L_rho(1-f). Its value is one over rho. Positivity of the norm of rho and of the square root permits division, and the nonempty-set characterization of infimum distance gives the result."),
            Theorem("nontrivial_zero_domain", "Domain of a nontrivial zero",
                Seq(Forall, Sp, Rho, InMacro, Sp, C, Comma, Sp,
                    App(Seq(Operatorname, Grp(F.Id("IsNontrivialZero"))), Rho), Rightarrow, Sp,
                    Re, Sp, Rho, Lt, D(1), Land, Sp, Rho, Neq, D(0), Land, Sp, Rho, Neq, D(1),
                    Land, Sp, D(0), Lt, Norm(Rho)),
                "IsNontrivialZero is the canonical Zeta23 predicate: zeta(rho) equals zero and zero less than Re(rho) less than one. This gives the upper strip bound, excludes zero and one, and makes the denominator positive."),
            Theorem("nyman_unitInterval_zero_obstruction", "The canonical-zero distance obstruction",
                Seq(Forall, Sp, Rho, InMacro, Sp, C, Comma, Sp,
                    App(Seq(Operatorname, Grp(F.Id("IsNontrivialZero"))), Rho), Rightarrow, Sp,
                    HalfPlane(Rho), Rightarrow, Sp, Distance),
                "Every actual nontrivial zero with real part greater than one half gives the stated lower bound on the unit-interval distance. This is conditional and asserts no existence of such a zero."),
            Theorem("nyman_unitInterval_mellin_and_zero_obstruction", "Mellin identity and zero obstruction together",
                Seq(Begin, Grp(F.Id("gathered")), Open, E9, Close, RowBreak, Land, Sp, Open, E10, Close,
                    End, Grp(F.Id("gathered"))),
                "The first conjunct states the fractional-part identity for every real theta in (0,1] and every complex s with zero less than Re(s) less than one. Independently, the second conjunct quantifies over all canonical nontrivial zeros with real part greater than one half, and states the exact norm, target value, annihilation of the whole closure, and distance lower bound. The underlying functional and all source vectors are those on H defined above.")), [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Weil/ZetaPntBounds/NymanFractionalMellin"))
        ]));
}
