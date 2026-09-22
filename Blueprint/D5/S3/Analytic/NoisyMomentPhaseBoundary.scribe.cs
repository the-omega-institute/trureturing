using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class NoisyMomentPhaseBoundaryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/NoisyMomentPhaseBoundary.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Assuming every nonconstant dual coefficient is nonzero, every feasible exterior mass satisfies the affine noisy-moment bound, whose equality case has a unique probability pair.",
        H("Noisy Moment Phase Boundary"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("noisy-moment-phase-exact-classification"),
                DeclarationHandle.Create(Prefix + "exact_noise_phase_classification"),
                H("Affine bound and exact equality classification"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For distinct real nodes and an off-node point, the Lagrange 0/1 dual polynomial determines P, the coefficient cost L, the signed perturbation r, and transition slopes A_i=P*r_i/c_i-L. Feas_epsilon(w,u,v) abbreviates exactly the normalized nonnegative weights and all-moment error bounds displayed in the theorem formula. Assuming every nonconstant dual coefficient is nonzero, every such feasible triple has a nonnegative dual gap 1+epsilon*L-w*P, equal to the sum of its nodal and nonconstant noisy-coordinate slacks; in particular, w*P is at most 1+epsilon*L. At w=(1+epsilon*L)/P, feasibility holds exactly when every epsilon*A_i is at most one and the two probability weights are the computed positive and negative parts. The equality decomposition forces each nonconstant noisy moment to saturate and then forces every nodal weight, while the converse construction verifies normalization and all moments. Equality at a transition constraint is included. The result classifies attainment of this affine bound; it makes no assertion about later optimal phases or zero dual coefficients."))),
                DescribeRole.Theorem))));

    private static Formula Indexed(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula Power(Formula value, Formula exponent) =>
        Seq(value, Caret, Grp(exponent));

    private static Formula SumOverI(Formula value) =>
        Seq(Sum, Underscore, Grp(F.Id("i")), Sp, value);

    private static Formula Abs(Formula value) => Seq(Lvert, Sp, value, Sp, Rvert);

    private static Formula MaxZero(Formula value) =>
        Seq(Max, Open, value, Comma, Sp, D(0), Close);

    private static Formula IfThenElse(Formula condition, Formula yes, Formula no) =>
        Call("if", condition, yes, no);

    private static Formula TheoremFormula()
    {
        Formula i = F.Id("i");
        Formula k = F.Id("k");
        Formula n = F.Id("N");
        Formula w = F.Id("w");
        Formula u = F.Id("u");
        Formula v = F.Id("v");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula p = F.Id("p");
        Formula bigP = F.Id("P");
        Formula bigL = F.Id("L");
        Formula epsilon = Varepsilon;
        Formula ci = Indexed(F.Id("c"), i);
        Formula ri = Indexed(F.Id("r"), i);
        Formula ai = Indexed(F.Id("A"), i);
        Formula bi = Indexed(F.Id("b"), i);
        Formula ui = Indexed(u, i);
        Formula vi = Indexed(v, i);
        Formula xi = Indexed(x, i);
        Formula pk = Indexed(p, k);
        Formula ek = Indexed(F.Id("e"), k);
        Formula dk = Indexed(F.Id("d"), k);
        Formula elli = Indexed(Ell, i);
        Formula wEpsilon = Indexed(w, epsilon);
        Formula pAtXi = Call("p", xi);
        Formula feasible = Call("Feas", epsilon, w, u, v);
        Formula feasibleAtAffine = Call("Feas", epsilon, wEpsilon, u, v);
        Formula kIsZero = Seq(k, Sp, Eq, Sp, D(0));
        Formula nonconstantAbs = IfThenElse(kIsZero, D(0), Abs(pk));
        Formula nonconstantNoise = IfThenElse(
            kIsZero, D(0), Seq(epsilon, Sp, Abs(pk)));
        Formula error = Seq(
            w, Sp, Power(y, k), Sp, Plus, Sp,
            SumOverI(Seq(ui, Sp, Power(xi, k))), Sp, Minus, Sp,
            SumOverI(Seq(vi, Sp, Power(xi, k))));
        Formula noiseSlack = Seq(
            nonconstantNoise, Sp, Minus, Sp, pk, Sp, ek);
        Formula nodalUSlack = Seq(ui, Sp, pAtXi);
        Formula nodalVSlack = Seq(vi, Sp, Open, D(1), Sp, Minus, Sp, pAtXi, Close);
        Formula gap = Seq(D(1), Sp, Plus, Sp, epsilon, Sp, bigL, Sp, Minus, Sp, w, bigP);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            D(1), Sp, Le, Sp, n, Comma, Sp,
            Open, Forall, Sp, i, Comma, Sp, k, Comma, Sp,
                i, Sp, Neq, Sp, k, Sp, Rightarrow, Sp,
                xi, Sp, Neq, Sp, Indexed(x, k), Close, Comma, Sp,
            Open, Forall, Sp, i, Comma, Sp, y, Sp, Neq, Sp, xi, Close,
            Comma, RowBreak, Grp(),
            elli, Sp, Eq, Sp, Call("Lagrange", x, i), Comma, Sp,
            ci, Sp, Eq, Sp, Call("eval", elli, y), Comma, Sp,
            p, Sp, Eq, Sp, Call("interpolate", x,
                Indexed(D(1), Grp(ci, Sp, Gt, Sp, D(0)))), Comma, RowBreak, Grp(),
            bigP, Sp, Eq, Sp, Call("p", y), Comma, Sp,
            bigL, Sp, Eq, Sp,
                Sum, Underscore, Grp(k, Sp, Lt, Sp, n), Sp,
                nonconstantAbs, Comma, RowBreak, Grp(),
            dk, Sp, Eq, Sp, IfThenElse(kIsZero, D(0),
                IfThenElse(Seq(D(0), Sp, Le, Sp, pk), D(1), Seq(Minus, D(1)))),
                Comma, Sp,
            ri, Sp, Eq, Sp,
                Sum, Underscore, Grp(k, Sp, Lt, Sp, n), Sp,
                dk, OpenBracket, elli, CloseBracket,
                    Underscore, Grp(k), Comma, RowBreak, Grp(),
            ek, Sp, Eq, Sp, error, Comma, Sp,
            Delta, Sp, Eq, Sp, gap, Comma, RowBreak, Grp(),
            ai, Sp, Eq, Sp, Frac, Grp(bigP, ri), Grp(ci), Sp, Minus, Sp, bigL,
            Comma, Sp, bi, Sp, Eq, Sp, wEpsilon, ci, Sp, Minus, Sp, epsilon, Sp, ri,
            Comma, Sp, wEpsilon, Sp, Eq, Sp,
            Frac, Grp(D(1), Sp, Plus, Sp, epsilon, Sp, bigL), Grp(bigP), Comma, RowBreak, Grp(),

            feasible, Sp, Leftrightarrow, Sp,
            Open,
            D(0), Sp, Le, Sp, w, Sp, Land, Sp,
            Open, Forall, Sp, i, Comma, Sp, D(0), Sp, Le, Sp, ui, Close, Sp, Land, Sp,
            Open, Forall, Sp, i, Comma, Sp, D(0), Sp, Le, Sp, vi, Close, Sp, Land, Sp,
            w, Sp, Plus, Sp, SumOverI(ui), Sp, Eq, Sp, D(1), Sp, Land, Sp,
            SumOverI(vi), Sp, Eq, Sp, D(1), Sp, Land, Sp,
            Open, Forall, Sp, k, Lt, n, Comma, Sp, Abs(ek), Sp, Le, Sp, epsilon, Close,
            Close, Comma, RowBreak, Grp(),

            Open, Forall, Sp, k, Comma, Sp,
                k, Sp, Lt, Sp, n, Sp, Rightarrow, Sp,
                k, Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp,
                pk, Sp, Neq, Sp, D(0), Close,
            Sp, Land, Sp, D(0), Sp, Le, Sp, epsilon,
            Sp, Longrightarrow, Sp, RowBreak, Grp(),

            Open, Forall, Sp, w, Comma, Sp, u, Comma, Sp, v, Comma, Sp,
                feasible, Sp, Rightarrow, Sp, Open,
                D(0), Sp, Le, Sp, Delta, Sp, Land, Sp,
                Open, Forall, Sp, i, Comma, Sp,
                    D(0), Sp, Le, Sp, nodalUSlack, Close, Sp, Land, Sp,
                Open, Forall, Sp, i, Comma, Sp,
                    D(0), Sp, Le, Sp, nodalVSlack, Close, Sp, Land, Sp,
                Open, Forall, Sp, k, Comma, Sp,
                    k, Sp, Lt, Sp, n, Sp,
                    Rightarrow, Sp, D(0), Sp, Le, Sp, noiseSlack, Close, Sp, Land, Sp,
                Delta, Sp, Eq, Sp,
                    SumOverI(nodalUSlack), Sp, Plus, Sp,
                    SumOverI(nodalVSlack), Sp, Plus, Sp,
                    Sum, Underscore, Grp(k, Sp, Lt, Sp, n), Sp,
                    Open, noiseSlack, Close,
                Close, Close, Sp, Land, Sp, RowBreak, Grp(),

            Open, Forall, Sp, u, Comma, Sp, v, Comma, Sp,
                feasibleAtAffine, Sp, Leftrightarrow, Sp, Open,
                Open, Forall, Sp, i, Comma, Sp, epsilon, Sp, ai, Sp, Le, Sp, D(1), Close,
                Sp, Land, Sp,
                u, Sp, Eq, Sp, Open, i, Sp, Mapsto, Sp,
                    MaxZero(Seq(Minus, bi)), Close, Sp, Land, Sp,
                v, Sp, Eq, Sp, Open, i, Sp, Mapsto, Sp,
                    MaxZero(bi), Close,
                Close, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
