using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class NoisyMeasurementCatOptimalityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/NoisyMeasurementCatOptimalityRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Estimation/len2022quantum");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Len, Gefen, Retzker and Kołodyński (arXiv:2109.01160, Nature Communications 13, 6971) conjecture that for every classical noise channel M_x = sum_i p(x|i) Pi_i applied independently to N probes, the pair of orthonormal states maximizing the noisy Fisher coefficient gamma can be taken of cat form cos(theta)|j>^N + sin(theta)|k>^N, -sin(theta)|j>^N + cos(theta)|k>^N. For a three-outcome qutrit detector with entries in (1/20)Z and two probes, the pair |10>, |21> attains a larger gamma than every cat pair.",
        H("Cat pairs need not be optimal for metrology with noisy measurements"),
        Blocks(
            Node("probe-op", "The single-probe noisy measurement", ProbeOpFormula(),
                "M_x = sum_i p(x|i) Pi_i, with Pi_i = |i><i| the matrix with a single 1 in position (i, i).",
                "probeOp", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("multi-probe-op", "Independent measurement of N probes", MultiProbeOpFormula(),
                "Eq. (AMxvec): M_x = M_{x_1} (x) ... (x) M_{x_N}. The frozen finite-family Kronecker equivalence piKroneckerLinearEquiv sends the tensor product of the single-probe matrices to a matrix on the words s : Fin N -> Fin d; its entry at (s, s') is the product over l of the entries of M_{x_l} at (s(l), s'(l)).",
                "multiProbeOp", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("gamma", "The noisy Fisher coefficient", GammaFormula(),
                "Eq. (AgammaN): gamma = (1/4) sum over outcome words of [<psi_perp|V^dagger M_x V|psi> + c.c.]^2 / <psi|V^dagger M_x V|psi>, where V psi = (zeta + zeta_perp)/sqrt(2) and V psi_perp = (zeta - zeta_perp)/sqrt(2) invert the relations V (psi +- psi_perp)/sqrt(2) = zeta, zeta_perp of Eq. (AVPhichoice). Here <a, b> = sum_s conj(a(s)) b(s) and M psi is the matrix-vector product. The real part reads the source quotient, whose numerator and denominator are real.",
                "gamma", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("basis-power", "Repeated basis words", BasisPowerFormula(),
                "|j>^N is the product of N copies of the basis vector |j> of the common eigenbasis.",
                "basisPower", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("cat-state", "The cat state", CatStateFormula(),
                "The first member of the conjectured optimal pair.",
                "catState", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("cat-perp", "Its orthogonal partner", CatPerpFormula(),
                "The second member of the conjectured optimal pair.",
                "catPerp", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjectured optimality of cat pairs", ClaimFormula(),
                "For every d >= 2, every finite outcome set X, every classical noise channel p with all entries positive, so that a maximizing pair exists, and every N >= 1 there are labels j != k and an angle theta whose cat pair attains the largest gamma among all orthonormal pairs. Orthonormality uses <a, b> = sum_s conj(a(s)) b(s). This is the weakest reading of the conjecture; it does not require j and k to be found from a single probe.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("detector", "The detector", DetectorFormula(),
                "Row x lists p(x|0), p(x|1), p(x|2); every column sums to 1 and every entry is at least 1/20.",
                "detector", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("witness", "The first witness state", WitnessFormula(),
                "The basis word 10 of two qutrits.",
                "witness", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("witness-perp", "The second witness state", WitnessPerpFormula(),
                "The basis word 21 of two qutrits.",
                "witnessPerp", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("result", "A crossed pair beats every cat pair", Disp(new Formula.Not(F.Id("claim"))),
                "Take d = 3, X = Fin 3, the detector above and N = 2. Write m_x(s) = p(x_1|s_1) p(x_2|s_2). For real orthonormal vectors supported on two words u != v the coefficient is gamma = sum_x t (1 - t) (m_x(u) - m_x(v))^2 / (t m_x(u) + (1 - t) m_x(v)), where t is the squared weight of u in (zeta + zeta_perp)/sqrt(2). The witness pair has u = 10, v = 21 and t = 1/2, and gamma = 6643859399/9075312000 > 73/100. Every cat pair with j != k has u = jj, v = kk and t = (cos(theta) - sin(theta))^2 / 2. Each summand is D - ab/D - (2t - 1)(a - b) with D = ta + (1 - t)b, and ab/D >= ab (2/D_0 - D/D_0^2) for D_0 = t_0 a + (1 - t_0) b, so gamma is bounded by an affine function of t. Evaluating it at t = 0 and t = 1 with t_0 = 2061/4000, 191/500, 1939/4000, 363/800, 309/500 or 437/800 for the six ordered pairs (j, k) gives gamma < 73/100. So no cat pair maximizes gamma.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("len-2022-noisy-metrology-cat-optimality"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("ncat-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(Formula name) => Seq(Operatorname, Grp(name));
    private static Formula Call(Formula name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Of(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula EqTo(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula LeTo(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Parenthesized(left), op, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula And(Formula left, Formula right) =>
        Logic(left, FormulaLogicOperator.And, right);
    private static Formula All(Formula variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, variable, Sp, Colon, Sp, domain, Comma, Sp, body);
    private static Formula Some(Formula variable, Formula domain, Formula body) =>
        Seq(Exists, Sp, variable, Sp, Colon, Sp, domain, Comma, Sp, body);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Frac(Formula top, Formula bottom) => new Formula.Fraction(top, bottom);
    private static Formula Pow(Formula b, Formula e) => new Formula.Power(b, e);
    private static Formula Root(Formula x) => Seq(Sqrt, Grp(x));
    private static Formula NumberSet(Formula name) => Seq(Mathbb, Grp(name));
    private static Formula Real() => NumberSet(F.Id("R"));
    private static Formula Complex() => NumberSet(F.Id("C"));
    private static Formula Nat() => NumberSet(F.Id("N"));
    private static Formula Fin(Formula n) => Call(F.Id("Fin"), n);
    private static Formula Arrow(Formula from, Formula to) => Seq(from, Sp, To, Sp, to);
    private static Formula Words(Formula n, Formula d) => Parenthesized(Arrow(Fin(n), Fin(d)));
    private static Formula Vectors(Formula n, Formula d) => Arrow(Words(n, d), Complex());
    private static Formula Channels(Formula x, Formula d) => Arrow(x, Arrow(Fin(d), Real()));
    private static Formula Vars(params Formula[] names)
    {
        var parts = new System.Collections.Generic.List<Formula>();
        for (var i = 0; i < names.Length; i++)
        {
            if (i > 0)
            {
                parts.Add(Comma);
                parts.Add(Sp);
            }
            parts.Add(names[i]);
        }
        return Seq([.. parts]);
    }
    private static Formula Tuple(params Formula[] items) => Parenthesized(Vars(items));
    private static Formula Ket(params byte[] digits) => Seq(Bar, D(digits), Rangle);
    private static Formula Cos(Formula x) => Call(F.Id("cos"), x);
    private static Formula SinOf(Formula x) => Call(F.Id("sin"), x);
    private static Formula Neg(Formula x) => Seq(Minus, x);
    private static Formula Inner(Formula left, Formula right) => Seq(Langle, Sp, left, Comma, Sp, right, Sp, Rangle);
    private static Formula Conj(Formula x) => Seq(Overline, Grp(x));
    private static Formula SumOver(Formula index, Formula body) => Seq(Sum, Underscore, Grp(index), Sp, body);
    private static Formula ProdOver(Formula index, Formula body) => Seq(Prod, Underscore, Grp(index), Sp, body);
    private static Formula Twentieths(params byte[][] numerators)
    {
        var items = new Formula[numerators.Length];
        for (var i = 0; i < numerators.Length; i++)
        {
            items[i] = Frac(D(numerators[i]), D(2, 0));
        }
        return Tuple(items);
    }

    private static Formula FiniteType(Formula x, Formula body) =>
        Seq(Forall, Sp, x, Sp, Colon, Sp, F.Id("Type"), Comma, Sp,
            OpenBracket, Call(F.Id("Fintype"), x), CloseBracket, Comma, Sp, body);

    private static Formula AnyPrelude(Formula body)
    {
        Formula d = F.Id("d"), x = F.Id("X"), p = F.Id("p");
        return All(d, Nat(), All(x, F.Id("Type"), All(p, Channels(x, d), body)));
    }

    private static Formula Prelude(Formula body)
    {
        Formula d = F.Id("d"), x = F.Id("X"), p = F.Id("p");
        return All(d, Nat(), FiniteType(x, All(p, Channels(x, d), body)));
    }

    private static Formula ProbeOpFormula()
    {
        Formula xo = F.Id("x"), i = F.Id("i"), x = F.Id("X"), p = F.Id("p");
        Formula value = SumOver(Seq(i, Sp, InMacro, Sp, Fin(F.Id("d"))),
            Mul(Of(p, xo, i), Call(F.Id("single"), i, i, D(1))));
        return Disp(AnyPrelude(All(xo, x, EqTo(Call(F.Id("probeOp"), p, xo), value))));
    }

    private static Formula MultiProbeOpFormula()
    {
        Formula n = F.Id("N"), xs = F.Id("xs"), l = F.Id("l"), p = F.Id("p");
        Formula factors = Parenthesized(Seq(l, Sp, Mapsto, Sp, Call(F.Id("probeOp"), p, Of(xs, l))));
        Formula value = Call(F.Id("piKroneckerLinearEquiv"), Call(F.Id("tprod"), factors));
        return Disp(AnyPrelude(All(n, Nat(), All(xs, Arrow(Fin(n), F.Id("X")),
            EqTo(Call(F.Id("multiProbeOp"), p, xs), value)))));
    }

    private static Formula GammaFormula()
    {
        Formula n = F.Id("N"), d = F.Id("d"), p = F.Id("p"), xs = F.Id("xs"), zeta = F.Id("zeta"),
            zetaP = F.Id("zetaperp"), psi = F.Id("psi"), psiP = F.Id("psiperp");
        Formula m = Call(F.Id("multiProbeOp"), p, xs);
        Formula z = Inner(psiP, Mul(m, psi));
        Formula term = Call(F.Id("Re"), Frac(Mul(Frac(D(1), D(4)), Pow(Parenthesized(Add(z, Conj(z))), D(2))),
            Inner(psi, Mul(m, psi))));
        Formula defs = And(EqTo(psi, Frac(Add(zeta, zetaP), Root(D(2)))),
            EqTo(psiP, Frac(Sub(zeta, zetaP), Root(D(2)))));
        Formula value = SumOver(Seq(xs, Sp, Colon, Sp, Arrow(Fin(n), F.Id("X"))), term);
        return Disp(Prelude(All(n, Nat(), All(Vars(zeta, zetaP, psi, psiP), Vectors(n, d),
            Imp(defs, EqTo(Call(F.Id("gamma"), p, zeta, zetaP), value))))));
    }

    private static Formula BasisPowerFormula()
    {
        Formula n = F.Id("N"), d = F.Id("d"), j = F.Id("j"), s = F.Id("s"), l = F.Id("l");
        Formula value = ProdOver(Seq(l, Sp, InMacro, Sp, Fin(n)),
            Of(Call(F.Id("PiSingle"), j, D(1)), Of(s, l)));
        return Disp(All(Vars(d, n), Nat(), All(j, Fin(d), All(s, Words(n, d),
            EqTo(Of(Call(F.Id("basisPower"), j), s), value)))));
    }

    private static Formula CatStateFormula()
    {
        Formula n = F.Id("N"), d = F.Id("d"), j = F.Id("j"), k = F.Id("k"), theta = Theta;
        Formula value = Add(Mul(Cos(theta), Call(F.Id("basisPower"), j)),
            Mul(SinOf(theta), Call(F.Id("basisPower"), k)));
        return Disp(All(Vars(d, n), Nat(), All(Vars(j, k), Fin(d), All(theta, Real(),
            EqTo(Call(F.Id("catState"), j, k, theta), value)))));
    }

    private static Formula CatPerpFormula()
    {
        Formula n = F.Id("N"), d = F.Id("d"), j = F.Id("j"), k = F.Id("k"), theta = Theta;
        Formula value = Add(Mul(Neg(SinOf(theta)), Call(F.Id("basisPower"), j)),
            Mul(Cos(theta), Call(F.Id("basisPower"), k)));
        return Disp(All(Vars(d, n), Nat(), All(Vars(j, k), Fin(d), All(theta, Real(),
            EqTo(Call(F.Id("catPerp"), j, k, theta), value)))));
    }

    private static Formula ClaimFormula()
    {
        Formula d = F.Id("d"), x = F.Id("X"), p = F.Id("p"), n = F.Id("N"), xo = F.Id("x"), i = F.Id("i"),
            j = F.Id("j"), k = F.Id("k"), theta = Theta, zeta = F.Id("zeta"), zetaP = F.Id("zetaperp");
        Formula positive = All(xo, x, All(i, Fin(d), Rel(D(0), FormulaRelationOperator.LessThan, Of(p, xo, i))));
        Formula columns = All(i, Fin(d), EqTo(SumOver(Seq(xo, Sp, InMacro, Sp, x), Of(p, xo, i)), D(1)));
        Formula orthonormal = And(And(EqTo(Inner(zeta, zeta), D(1)), EqTo(Inner(zetaP, zetaP), D(1))),
            EqTo(Inner(zetaP, zeta), D(0)));
        Formula best = LeTo(Call(F.Id("gamma"), p, zeta, zetaP),
            Call(F.Id("gamma"), p, Call(F.Id("catState"), j, k, theta), Call(F.Id("catPerp"), j, k, theta)));
        Formula pair = Some(Vars(j, k), Fin(d), And(Rel(j, FormulaRelationOperator.NotEqual, k),
            Some(theta, Real(), All(Vars(zeta, zetaP), Vectors(n, d), Imp(orthonormal, best)))));
        Formula body = Imp(Rel(D(2), FormulaRelationOperator.LessThanOrEqual, d),
            FiniteType(x, All(p, Channels(x, d), Imp(And(positive, columns),
                All(n, Nat(), Imp(Rel(D(1), FormulaRelationOperator.LessThanOrEqual, n), pair))))));
        return Disp(Logic(F.Id("claim"), FormulaLogicOperator.Iff, All(d, Nat(), body)));
    }

    private static Formula DetectorFormula()
    {
        Formula det = F.Id("detector");
        return Disp(And(And(EqTo(Of(det, D(0)), Twentieths([1], [1, 4], [2])),
            EqTo(Of(det, D(1)), Twentieths([1, 5], [2], [1, 7]))),
            EqTo(Of(det, D(2)), Twentieths([4], [4], [1]))));
    }

    private static Formula WitnessFormula() => Disp(EqTo(F.Id("witness"), Ket(1, 0)));

    private static Formula WitnessPerpFormula() => Disp(EqTo(F.Id("witnessPerp"), Ket(2, 1)));
}
