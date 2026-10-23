using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class SharpTrajectoryNoiseRecoveryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact deterministic recovery from Hilbert trajectories", H("Exact deterministic recovery from Hilbert trajectories"), Blocks(
            Paragraph(Text("Throughout, K is the real or complex field, E is a nonzero complete Hilbert space over K, and F is a complete Hilbert space over K. All observation operators are bounded and linear. No dimension, separability, compactness or surjectivity assumption is imposed.")),
            Paragraph(Text("For A:E→F define m(A)=inf{‖Ax‖²:‖x‖=1}. For an arbitrary total function Q:F→E and a real budget δ≥0, define e(A,δ,Q)=sup{ofReal(‖Q(Ax+η)−x‖):x∈E, η∈F, ‖η‖≤δ}. The supremum and infimum of risks are in ENNReal; a reconstruction may have infinite worst-case risk. The lower modulus is a genuine real infimum and need not be attained.")),
            Describe.Lean(DescribeId.Create("sharp-hilbert-noise-recovery"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/SharpTrajectoryNoiseRecovery.sharp_hilbert_noise_recovery"),
                H("A total least-squares inverse attains the sharp minimax risk"), StatementSource.FromAuthor(Hilbert()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every bounded A with m(A)>0 there is one bounded linear R:F→E satisfying all the displayed properties simultaneously for every finite real δ≥0. The infimum ranges over every total reconstruction function, including nonlinear and discontinuous functions. In particular the exact risk at δ=0 is zero.")),
                    Paragraph(Text("The positive modulus makes A injective with closed range. Let P be the orthogonal projection onto that range and let R=(A restricted to its range)⁻¹ P. Thus R is defined on all of F. Its residual y−ARy is orthogonal to every Ax, so it is the Moore–Penrose least-squares left inverse. Projection contraction and the lower modulus give the stated norm estimate and risk upper bound.")),
                    Paragraph(Text("For the lower bound, opposite states z and −z with noises −Az and Az produce the same zero datum whenever ‖Az‖≤δ. The triangle inequality forces at least one error to be at least ‖z‖. Scaling every unit direction and taking the defining infimum yields δ/sqrt(m(A)); no minimizing direction or continuity of the reconstruction is used. Infinite risk is handled directly in ENNReal."))), DescribeRole.Theorem),
            Paragraph(Text("For bounded B:E→E and C:E→F and T>0, put H_T=L²(F,volume restricted to (0,T]), with the ordinary unnormalized Lebesgue measure. Define E_T(x)=∫₀ᵀ‖C exp(tB)x‖²dt and a(T)=inf{E_T(x):‖x‖=1}. Equality of representatives below is almost everywhere for this restricted measure.")),
            Describe.Lean(DescribeId.Create("sharp-trajectory-noise-recovery"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/SharpTrajectoryNoiseRecovery.sharp_trajectory_noise_recovery"),
                H("The actual Lebesgue L² trajectory has the exact noise constant"), StatementSource.FromAuthor(Trajectory()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Assume a(T)>0. The theorem constructs the actual bounded trajectory operator A:E→H_T, proves its almost-everywhere representative and the exact identity ‖Ax‖²=E_T(x), and identifies m(A)=a(T). It then constructs a total bounded linear R:H_T→E with left-inverse, normal-equation and norm-bound properties. The same R attains both exact risk identities for every finite real δ≥0.")),
                    Paragraph(Text("Continuity of the operator-valued exponential on the compact window provides a uniform operator-norm bound, which constructs the L² operator. The Hilbert L² inner-product formula gives the unnormalized integral identity. The general sharp recovery theorem then applies with the exact trajectory floor. A positive certified lower bound 0<α≤a(T) gives an upper estimate δ/sqrt(α), but does not replace a(T) in the sharp equality.")),
                    Paragraph(Text("These are classical Hilbert-space consequences assembled with the trajectory and unrestricted risk models. The theorem makes no claim for a(T)=0 or T=0. Window equivalence, matching short-window powers and moment clauses are separate statements."))), DescribeRole.Theorem))));

    private static Formula Hilbert()
    {
        Formula a = F.Id("A"), r = F.Id("R"), q = F.Id("Q"), d = DeltaLower, x = F.Id("x"), y = F.Id("y"),
            e = F.Id("E"), f = F.Id("F"), m = App(F.Id("m"), a);
        return Disp(Seq(Forall, Sp, F.Id("K"), Comma, Sp, e, Comma, Sp, f, Sp,
            App(F.Id("Hilbert"), F.Id("K"), e, f), Comma, Sp, e, Neq, D(0), Comma, Sp,
            Forall, Sp, a, Colon, App(F.Id("BoundedLinear"), e, f), Comma, Sp, D(0), Lt, m,
            Rightarrow, RowBreak, Grp(), Exists, Sp, r, Colon, App(F.Id("BoundedLinear"), f, e), Comma, Sp,
            Properties(a, r, x, y, m), Sp, Land, RowBreak, Grp(),
            Forall, Sp, d, InMacro, Mathbb, Grp(F.Id("R")), Comma, Sp, D(0), Le, d, Rightarrow, Sp,
            RiskIdentities(a, r, q, d, m, f, e)));
    }

    private static Formula Trajectory()
    {
        Formula b = F.Id("B"), c = F.Id("C"), t = F.Id("T"), a = F.Id("A"), r = F.Id("R"),
            q = F.Id("Q"), x = F.Id("x"), y = F.Id("y"), s = F.Id("s"), e = F.Id("E"), f = F.Id("F"),
            h = Sub(F.Id("H"), t), floor = App(F.Id("a"), t), d = DeltaLower;
        return Disp(Seq(Forall, Sp, F.Id("K"), Comma, Sp, e, Comma, Sp, f, Sp,
            App(F.Id("Hilbert"), F.Id("K"), e, f), Comma, Sp, e, Neq, D(0), Comma, Sp,
            Forall, Sp, b, Colon, App(F.Id("BoundedLinear"), e, e), Comma, Sp,
            c, Colon, App(F.Id("BoundedLinear"), e, f), Comma, Sp,
            t, InMacro, Mathbb, Grp(F.Id("R")), Comma, Sp, D(0), Lt, t, Sp, Land, Sp, D(0), Lt, floor,
            Rightarrow, RowBreak, Grp(), Exists, Sp, a, Colon, App(F.Id("BoundedLinear"), e, h), Comma, Sp,
            Exists, Sp, r, Colon, App(F.Id("BoundedLinear"), h, e), Comma, RowBreak, Grp(),
            Open, Forall, Sp, x, Comma, Sp, App(a, x), Sub(Eq, F.Id("ae")), Open, s, Mapsto, Sp,
            App(c, App(App(F.Id("exp"), Seq(s, b)), x)), Close, Close, Sp, Land, Sp,
            Open, Forall, Sp, x, Comma, Sp, Pow(Norm(App(a, x)), D(2)), Eq,
            App(Sub(F.Id("E"), t), x), Close, Sp, Land, Sp, App(F.Id("m"), a), Eq, floor, Sp, Land,
            RowBreak, Grp(), Properties(a, r, x, y, floor), Sp, Land, RowBreak, Grp(),
            Forall, Sp, d, InMacro, Mathbb, Grp(F.Id("R")), Comma, Sp, D(0), Le, d, Rightarrow, Sp,
            RiskIdentities(a, r, q, d, floor, h, e)));
    }

    private static Formula Properties(Formula a, Formula r, Formula x, Formula y, Formula m) => Seq(
        Open, Forall, Sp, x, Comma, Sp, App(r, App(a, x)), Eq, x, Close, Sp, Land, Sp,
        Open, Forall, Sp, y, Comma, Sp, x, Comma, Sp, Langle, Sp, App(a, x), Comma,
        Seq(y, Minus, App(a, App(r, y))), Rangle, Eq, D(0), Close, Sp, Land, Sp,
        Open, Forall, Sp, y, Comma, Sp, Norm(App(r, y)), Le, Fraction(Norm(y), Seq(Sqrt, Grp(m))), Close);

    private static Formula RiskIdentities(Formula a, Formula r, Formula q, Formula d, Formula m, Formula f, Formula e)
    {
        Formula value = App(F.Id("ofReal"), Fraction(d, Seq(Sqrt, Grp(m))));
        return Seq(App(F.Id("e"), a, d, r), Eq, value, Sp, Land, Sp,
            Sub(F.Id("inf"), Seq(q, Colon, f, To, Sp, e)), App(F.Id("e"), a, d, q), Eq, value);
    }
    private static Formula Fraction(Formula x, Formula y) => Seq(Frac, Grp(x), Grp(y));
    private static Formula Norm(Formula x) => Seq(Vert, Sp, x, Vert);
    private static Formula Pow(Formula x, Formula n) => Seq(x, Caret, Grp(n));
    private static Formula Sub(Formula x, Formula n) => Seq(x, Underscore, Grp(n));
    private static Formula App(Formula f, params Formula[] xs) => new Formula.Apply(f, [.. xs]);
}
