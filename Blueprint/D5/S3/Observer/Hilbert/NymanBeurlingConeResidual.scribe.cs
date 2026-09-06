using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Hilbert;

internal sealed class NymanBeurlingConeResidualDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Hilbert/NymanBeurlingConeResidual.";
    private static Formula Hc => Seq(Mathcal, Grp(F.Id("H")));
    private static Formula C => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula M => F.Id("M");
    private static Formula K => F.Id("K");
    private static Formula Chi => Seq(Mathrm, Grp(F.Id("chi")));
    private static Formula P => F.Id("p");
    private static Formula Res => F.Id("r");
    private static Formula W => F.Id("w");
    private static Formula X => F.Id("x");
    private static Formula S => F.Id("s");
    private static Formula N => F.Id("N");
    private static Formula Orth => Seq(M, Caret, Grp(Perp));
    private static Formula Dual => Call("dual", K);
    private static Formula Sub(Formula a, Formula i) => Seq(a, Underscore, Grp(i));
    private static Formula Shell(Formula n) => Sub(F.Id("S"), n);
    private static Formula Call(string name, Formula a) =>
        Seq(Operatorname, Grp(F.Id(name)), Open, a, Close);
    private static Formula Closure(Formula a) => Seq(Overline, Grp(a));
    private static Formula Proj(Formula a, Formula x) => Seq(Sub(F.Id("P"), a), x);
    private static Formula Inner(Formula scalar, Formula a, Formula b) =>
        Sub(Seq(Langle, Sp, a, Comma, Sp, b, Rangle), scalar);
    private static Formula In(Formula a, Formula b) => Seq(a, InMacro, Sp, b);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Iffn(Formula a, Formula b) => Seq(a, Sp, Iff, Sp, b);
    private static Formula All(Formula a, Formula domain) =>
        Seq(Forall, Sp, a, InMacro, Sp, domain, Comma, Sp);
    private static Formula AllShells => Seq(OpenBrace, In(X, Hc), Sp, Mid, Sp,
        Exists, Sp, In(N, Nat), Comma, Sp, In(X, Shell(N)), CloseBrace);
    private static Formula PositiveShells =>
        Seq(OpenBrace, In(X, Hc), Sp, Mid, Sp, Exists, Sp, In(N, Nat), Comma, Sp,
            D(0), Lt, N, Sp, Land, Sp, In(X, Shell(N)), CloseBrace);
    private static Formula SqNorm(Formula a) => Seq(Vert, Sp, a, Vert, Caret, Grp(D(2)));
    private static Formula NegativeSquare => Seq(Minus, SqNorm(Res));
    private static Formula Neg(Formula a) => Seq(Minus, a);
    private static Formula Both(Formula a, Formula b) => Seq(a, Sp, Land, Sp, b);
    private static Formula Nonmember => Seq(F.Neg, Sp, Open, In(Chi, M), Close);

    private static DocumentBlock Claim(string name, string title, Formula statement, string prose) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The orthogonal residual of the actual Nyman target in its full complex arithmetic span "
        + "is the real-cone residual, and its negative is a dual witness.",
        H("Nyman-Beurling Cone Residual"),
        Blocks(
            Paragraph(Text(
                "H is exactly NymanBeurlingFiniteGramDistance.Carrier: Lp Complex 2 "
                + "positiveMeasure, with positiveMeasure equal to volume restricted to (0,infinity). "
                + "The existing target chi is the Lp class of the indicator of (0,1), with "
                + "squared norm one. The existing sourceVector a ha, for natural a and ha : 1 <= a, "
                + "is denoted f_a and represents ofReal(fract(1/(a*x))) almost everywhere. These are the source "
                + "owner's target_coe_ae, sourceVector_coe_ae and target_norm_sq facts.")),
            Paragraph(Text(
                "S_N is the existing complex span of sourceVector(i+1), i : Fin N. "
                + "M is BoundedInverseLimitReconstruction.cumulativeSpace shell, exactly the "
                + "topological closure of the supremum of all complex shells. K is the real "
                + "ProperCone obtained by restricting M's scalars to the nonnegative reals. "
                + "Its underlying set, norm and topology stay on the identical Lp carrier. "
                + "P_M and P_(M orthogonal) are the existing complex starProjection operators; "
                + "P_K is ConeResidualWitness.coneProjection. Define p=P_M chi, "
                + "r=P_(M orthogonal) chi and w=-r independently of P_K. "
                + "The notation dual(K) uses the nonnegative real inner pairing. Polar membership of y is "
                + "written -y in K dual, following MoreauDecomposition.")),
            Claim("shell_monotone", "Nested source shells",
                Seq(All(F.Id("n"), Nat), All(F.Id("m"), Nat), F.Id("n"), Le, Sp, F.Id("m"),
                    Rightarrow, Sp, Shell(F.Id("n")), Subseteq, Sp, Shell(F.Id("m"))),
                "Every finite source generator survives in every later complex span."),
            Claim("shell_zero", "Zero shell", Eqn(Shell(D(0)), Seq(OpenBrace, D(0), CloseBrace)),
                "The span indexed by Fin 0 is the bottom submodule."),
            Claim("cumulative_eq_closure_union", "Full arithmetic closure",
                Eqn(M, Closure(AllShells)), "Monotonicity identifies the submodule supremum with the union."),
            Claim("shell_union_eq_positive_union", "Positive source indices",
                Eqn(AllShells, PositiveShells),
                "The zero shell contributes no new vector: it is included in shell one. "
                + "The displayed positive-N union is the source union."),
            Claim("cumulative_eq_closure_positive_union", "Source completion",
                Eqn(M, Closure(PositiveShells)), "Both closure operations use the existing Lp topology."),
            Claim("shell_le_cumulative", "Every shell is retained",
                Seq(All(N, Nat), Shell(N), Subseteq, Sp, M),
                "This holds for every natural stage, including zero."),
            Claim("sourceVector_mem", "Every positive generator is retained",
                Seq(All(F.Id("n"), Nat), Both(
                    In(Sub(F.Id("f"), Seq(F.Id("n"), Plus, D(1))), Shell(Seq(F.Id("n"), Plus, D(1)))),
                    In(Sub(F.Id("f"), Seq(F.Id("n"), Plus, D(1))), M))),
                "The positivity proof for n+1 is derived. No arithmetic generator is omitted."),
            Claim("complex_smul_mem", "Full complex scalar closure",
                Seq(All(F.Id("c"), C), All(S, Hc), In(S, M), Rightarrow, Sp,
                    In(Seq(F.Id("c"), S), M)),
                "In particular multiplication by the imaginary unit stays in M; this is "
                + "not the real span of the displayed generators."),
            Claim("residualSpace_eq", "Existing residual owner",
                Eqn(Call("residualSpace", F.Id("shell")), Orth),
                "The infinite residual uses the same cumulativeSpace owner."),
            Claim("mem_cone", "Unchanged closed set", Seq(All(X, Hc), Iffn(In(X, K), In(X, M))),
                "Restriction of scalars changes neither membership nor the ambient carrier."),
            Claim("real_inner_eq", "Scalar pairing identification",
                Seq(All(X, Hc), All(F.Id("y"), Hc),
                    Eqn(Inner(R, X, F.Id("y")), Call("Re", Inner(C, X, F.Id("y"))))),
                "This uses the existing L2 real and complex inner products and commutation "
                + "of the real part with the integral. No global instance is installed."),
            Claim("coneProjection_eq", "Independent projections agree",
                Seq(All(X, Hc), Eqn(Proj(K, X), Proj(M, X))),
                "The chosen cone nearest point satisfies the complex submodule's existing "
                + "nearest-point characterization, which determines starProjection uniquely."),
            Claim("cone_residual_eq", "All-vector residual identity",
                Seq(All(X, Hc), Eqn(Seq(X, Minus, Proj(K, X)), Proj(Orth, X))),
                "The identity holds on the whole actual Lp carrier, beyond finite shells."),
            Claim("mem_innerDual_iff", "Dual is the complex orthogonal complement",
                Seq(All(W, Hc), Iffn(In(W, Dual), In(W, Orth))),
                "Testing a vector and its negative forces zero real pairing. Testing the "
                + "imaginary multiple then forces the imaginary pairing to vanish as well. "
                + "The reverse direction uses complex orthogonality."),
            Claim("mem_polar_iff", "Polar is the same orthogonal complement",
                Seq(All(W, Hc), Iffn(In(Neg(W), Dual), In(W, Orth))),
                "Both implications preserve the full complex orthogonal complement."),
            Claim("cone_signs", "Exact dual and polar signs",
                Seq(All(W, Hc), Both(
                    Seq(Open, Iffn(In(W, Dual),
                        Seq(Open, All(S, K), D(0), Le, Sp, Inner(R, S, W), Close)), Close),
                    Seq(Open, Iffn(In(Neg(W), Dual),
                        Seq(Open, All(S, K), Inner(R, W, S), Le, D(0), Close)), Close))),
                "The dual uses inner(s,w) >= 0; the polar uses inner(w,s) <= 0. "
                + "Real symmetry reconciles the argument order."),
            Claim("nyman_beurling_cone_residual", "Actual Nyman residual and witness",
                Seq(Begin, Grp(F.Id("gathered")),
                    Eqn(Chi, Seq(P, Plus, Res)), Sp, Land, Sp, In(P, M), Sp, Land, Sp, In(Res, Orth), RowBreak,
                    Land, Sp, Eqn(Inner(C, P, Res), D(0)), RowBreak,
                    Land, Sp, Eqn(Res, Seq(Chi, Minus, Proj(K, Chi))), RowBreak,
                    Land, Sp, In(W, Dual), Sp, Land, Sp, In(Neg(Res), Dual), RowBreak,
                    Land, Sp, Open, All(S, Hc), In(S, M), Rightarrow, Sp,
                    Open, Both(Eqn(Inner(C, W, S), D(0)), Eqn(Inner(R, W, S), D(0))), Close, Close, RowBreak,
                    Land, Sp, Eqn(Inner(R, W, Chi), NegativeSquare), RowBreak,
                    Land, Sp, Open, Iffn(Eqn(Res, D(0)), In(Chi, M)), Close, RowBreak,
                    Land, Sp, Open, Nonmember, Rightarrow, Sp, Inner(R, W, Chi), Lt, D(0), Close,
                    End, Grp(F.Id("gathered"))),
                "The carrier, target, infinite complex span and independently defined p, r, w "
                + "are fixed above. The decomposition uses Moreau; the generic cone residual "
                + "duality supplies the witness and conditional strict negativity. The "
                + "negative-square identity itself is unconditional. This is the Nyman "
                + "closed-subspace row only. It proves no nonmembership, nonzero residual, "
                + "vanishing residual, density or Riemann-hypothesis statement. The separate "
                + "analytic Nyman-Beurling equivalence and the other three cone rows remain open."))));
}
