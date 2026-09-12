using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.EntireGrowth;

internal sealed class RealExponentialDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Analytic/EntireGrowth/RealExponential.";
    private static Formula X => F.Id("x");
    private static Formula Y => F.Id("y");
    private static Formula R => F.Id("r");
    private static Formula C => F.Id("C");
    private static Formula T => F.Id("tau");
    private static Formula P => F.Id("rho");
    private static Formula B => F.Id("b");
    private static Formula N => F.Id("n");
    private static Formula Z => F.Id("z");
    private static Formula W => F.Id("w");
    private static Formula FX => Call("f", X);
    private static Formula RX => Call("r", X);
    private static Formula FZ => Call("f", Z);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Logarithmic growth and exponential norm bounds convert into one another; "
            + "quadratic factors are absorbed by every positive real power in the exponent.",
        H("Real exponential growth"),
        Blocks(
            Result("log-exp", "log_one_add_exp_le_add_log_two", "Logarithm of one plus an exponential",
                "For every nonnegative real x, the displayed bound holds. The proof bounds "
                    + "one plus exp(x) by twice exp(x), then uses monotonicity of the real logarithm.",
                Bound(Lg(Add(Num(1), Ex(X))), Add(X, Lg(Num(2))))),
            Result("log-comparison", "log_one_add_le_add_log_two_of_le_exp", "Transport an exponential bound",
                "For real x and y, assume both are nonnegative and y is at most exp(x). "
                    + "Monotonicity transports the preceding estimate to one plus y.",
                Bound(Lg(Add(Num(1), Y)), Add(X, Lg(Num(2))))),
            Result("exp-comparison", "le_exp_of_log_one_add_le", "Recover an exponential bound",
                "For arbitrary real x and nonnegative real y, a bound log(1+y) at most x "
                    + "implies the displayed inequality. No nonnegativity assumption on x is imposed.",
                Bound(Y, Ex(X))),
            Result("self-exp", "le_exp_self", "An exponential dominates its argument",
                "Every real x is at most exp(x). This follows from the standard tangent-line "
                    + "inequality one plus x at most exp(x), including negative x.",
                Bound(X, Ex(X))),
            Result("log-norm", "log_norm_le_log_one_add_norm", "A logarithmic norm comparison",
                "For every element w of an arbitrary seminormed additive commutative group, "
                    + "the displayed inequality holds. Zero norm is treated using the total real logarithm.",
                Bound(Lg(Norm(W)), Lg(Add(Num(1), Norm(W))))),
            Result("log-radius", "log_nonneg_mul_inv_norm_of_norm_le", "Nonnegative radius ratio logarithm",
                "In any normed additive commutative group, assume the norm of z is at most "
                    + "the real radius r. The logarithm of r times the inverse norm is nonnegative. "
                    + "The case z equals zero is included, with total inversion and logarithm.",
                Bound(Num(0), Lg(Mul(R, Inv(Norm(Z)))))),
            Result("log-two-radius", "log_two_le_log_two_mul_mul_inv_norm_of_norm_le", "A doubled radius ratio",
                "For nonzero z in any normed additive commutative group, if its norm is at "
                    + "most the real radius R, the displayed logarithm is at least log(2).",
                Bound(Lg(Num(2)), Lg(Mul(Mul(Num(2), F.Id("R")), Inv(Norm(Z)))))),
            Result("exponent", "norm_le_exp_mul_rpow_of_exponent_le", "Increase the growth exponent",
                "Let f map any index type into a seminormed additive commutative group, and "
                    + "let r be a real radius function with r(x) at least one for every x. "
                    + "For nonnegative C and real rho at most tau, a pointwise norm bound "
                    + "exp(C r(x)^rho) implies the displayed bound at every x.",
                AllX(Bound(Norm(FX), Ex(Mul(C, Pow(RX, T)))))),
            Result("log-to-exp", "norm_le_exp_mul_rpow_of_log_growth", "From logarithmic to exponential growth",
                "With the same arbitrary index and seminormed codomain, assume C is nonnegative, "
                    + "all radii are at least one, and rho is at most tau. A pointwise bound "
                    + "log(1+norm(f(x))) at most C r(x)^rho implies the displayed norm bound.",
                AllX(Bound(Norm(FX), Ex(Mul(C, Pow(RX, T)))))),
            Result("exp-to-log", "log_growth_of_norm_le_exp_mul_rpow", "From exponential to logarithmic growth",
                "For an arbitrary index type and seminormed codomain, assume C is positive, "
                    + "tau is nonnegative, every radius is at least one, and the norm of f(x) "
                    + "is at most exp(C r(x)^tau) for every x. There is a positive constant "
                    + "Cprime satisfying the displayed bound for every x. One may take C plus log(2).",
                ExistsPositive("Cprime", AllX(Bound(Lg(Add(Num(1), Norm(FX))),
                    Mul(F.Id("Cprime"), Pow(RX, T)))))),
            Result("natural-exponent", "exists_norm_le_exp_mul_pow_of_rpow_bound", "Pass to a natural exponent",
                "For an arbitrary index type, seminormed codomain, and radii at least one, "
                    + "let tau be real and n natural with tau strictly less than n. If a positive "
                    + "constant gives an exponential norm bound with real exponent tau, a positive "
                    + "constant gives the displayed bound with the ordinary natural power n.",
                ExistsPositive("C", AllX(Bound(Norm(FX), Ex(Mul(C, Pow(RX, N))))))),
            Result("quadratic", "sq_le_exp_const_mul_rpow", "Absorb a quadratic factor",
                "For every positive real b and every real r at least one, the displayed bound "
                    + "holds. Bounding log(r) by a real power and then exponentiating absorbs "
                    + "the quadratic factor with the explicit constant four divided by b.",
                Bound(Pow(R, Num(2)), Ex(Mul(Div(Num(4), B), Pow(R, B))))),
            Result("radius", "one_add_le_three_mul_one_add_of_le_two_mul_max", "Compare shifted radii",
                "For nonnegative real x and any real r at most twice max(x,1), the displayed "
                    + "inequality holds. It follows by bounding max(x,1) by one plus x.",
                Bound(Add(Num(1), R), Mul(Num(3), Parens(Add(Num(1), X))))),
            Result("radius-exp", "exp_mul_rpow_le_exp_mul_rpow_of_le_mul", "Rescale an exponential bound",
                "Let A, B, x, y, and tau be nonnegative real numbers with x at most B times y. "
                    + "Monotonicity of real powers and the multiplicative power identity give "
                    + "the displayed comparison, with all zero boundary cases included.",
                Bound(Ex(Mul(F.Id("A"), Pow(X, T))),
                    Ex(Mul(Mul(F.Id("A"), Pow(F.Id("B"), T)), Pow(Y, T))))),
            Result("floor", "exists_between_self_and_floor_add_one_same_floor", "A larger exponent with the same floor",
                "For each nonnegative real rho, there exists a real tau strictly between rho "
                    + "and its natural floor plus one. Tau is nonnegative and has the same natural "
                    + "floor as rho. The midpoint of that interval supplies such an exponent.",
                Seq(Seq(Exists, Sp, T, Comma, P, Lt, T, Land,
                    T, Lt, Add(Call("floorNat", P), Num(1)), Land, Num(0), Le, T, Land,
                    Call("floorNat", T), Eq, Call("floorNat", P)))),
            Result("sphere", "log_norm_le_of_log_one_add_growth_on_sphere", "Restrict growth to a sphere",
                "For any complex function f and real C, rho, and R, assume the global bound "
                    + "log(1+norm(f(z))) at most C (1+norm(z))^rho for every complex z. "
                    + "At every point on the sphere centered at zero with radius absolute R, "
                    + "the displayed estimate holds. Neither C nor rho is assumed nonnegative.",
                Bound(Lg(Norm(FZ)), Mul(C, Pow(Parens(Add(Num(1), Call("abs", F.Id("R")))), P)))),
            Result("order", "EntireOfOrderAtMost", "Entire order as an epsilon family",
                "For real rho and a complex function f, EntireOfOrderAtMost means complex "
                    + "differentiability everywhere together with the following condition: for "
                    + "every positive real epsilon there exists a positive real C, independent of z, "
                    + "bounding the norm at every complex z by exp(C (1+norm(z))^(rho+epsilon)). "
                    + "This definition does not identify order with a limsup or infimum definition.",
                Seq(Seq(Call("EntireOfOrderAtMost", P, F.Id("f")), Iff,
                    Call("Differentiable", Seq(Mathbb, Grp(F.Id("C"))), F.Id("f")), Land,
                    Forall, F.Id("epsilon"), Gt, Num(0), Comma,
                    Exists, C, Gt, Num(0), Comma, Forall, Z, Comma,
                    Norm(FZ), Le, Ex(Mul(C, Pow(Parens(Add(Num(1), Norm(Z))),
                        Add(P, F.Id("epsilon"))))))), DescribeRole.Definition),
            Result("order-differentiable", "differentiable", "Differentiability of an entire-order function",
                "For every real rho and every complex function f satisfying EntireOfOrderAtMost "
                    + "rho f, the function is complex differentiable everywhere.",
                Seq(Call("Differentiable", Seq(Mathbb, Grp(F.Id("C"))), F.Id("f")))),
            Result("order-bound", "exists_bound", "Extract a bound at a positive margin",
                "For every real rho, every positive real epsilon, and every complex function f "
                    + "satisfying EntireOfOrderAtMost rho f, there is a positive real C such that "
                    + "the displayed estimate holds at every complex z.",
                ExistsPositive("C", Seq(Seq(Forall, Z, Comma, Norm(FZ), Le,
                    Ex(Mul(C, Pow(Parens(Add(Num(1), Norm(Z))), Add(P, F.Id("epsilon"))))))))))));

    private static DocumentBlock Result(string id, string declaration, string title, string prose,
        Formula formula, DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("growth-" + id), DeclarationHandle.Create(Module + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Analytic/cipollina2026growth")),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Seq(params Formula[] terms) =>
        F.Seq(terms.SelectMany(term => new[] { term, F.Sp }).ToArray());

    private static Formula Add(Formula a, Formula b) => Seq(a, Plus, b);
    private static Formula Parens(Formula a) => Seq(Open, a, Close);
    private static Formula Mul(Formula a, Formula b) => Seq(Grp(a), Cdot, Grp(b));
    private static Formula Div(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Pow(Formula a, Formula b) => Seq(Grp(a), Caret, Grp(b));
    private static Formula Inv(Formula a) => Pow(a, Seq(Minus, Num(1)));
    private static Formula Lg(Formula a) => Call("log", a);
    private static Formula Ex(Formula a) => Call("exp", a);
    private static Formula Norm(Formula a) => Call("norm", a);
    private static Formula Bound(Formula a, Formula b) => Seq(Seq(a, Le, b));
    private static Formula AllX(Formula body) => Seq(Forall, X, Comma, body);
    private static Formula ExistsPositive(string name, Formula body) =>
        Seq(Exists, F.Id(name), Gt, Num(0), Comma, body);
}
