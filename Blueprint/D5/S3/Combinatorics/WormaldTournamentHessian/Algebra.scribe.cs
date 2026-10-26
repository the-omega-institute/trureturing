using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.WormaldTournamentHessian;

internal sealed class AlgebraDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Regular tournament Hessians: algebra.",
        H("Tournament Hessian: algebra"), Blocks(
            Helper("skewDiag", "The skew diagonal vanishes", WithA(All("i", Index,
                Eqn(Call("skewAdjacency", V("A"), V("i"), V("i")), D(0)))),
                "Subtracting a matrix from its transpose cancels the diagonal. This identifies the diagonal of each shifted matrix."),
            Helper("skewNormLe", "Skew entries are bounded by one", WithA(All("i", Index, All("j", Index,
                Le(Call("Norm.norm", new Formula.Apply(Call("Int.castRingHom", C), [Call("skewAdjacency", V("A"), V("i"), V("j"))])), D(1))))),
                "A difference of Boolean adjacency entries is −1, zero or one. Its complex norm is at most one."),
            Helper("shiftedDetNeZero", "Strict diagonal dominance", WithA(All("c", C,
                Imp(Eqn(Call("Norm.norm", V("c")), V("d")), Ne(Call("Matrix.det", Shift(V("c"))), D(0))))),
                "The diagonal has norm d and the sum of the other entry norms in each row is at most d−1. Gershgorin's strict diagonal-dominance consequence gives a nonzero determinant. No tournament or parity assumption is needed."),
            Helper("shiftedDetPureImaginary", "The imaginary shift in odd dimension", WithA(Imp(Call("Odd", V("d")),
                Eqn(Call("Complex.re", ImagDet), D(0)))),
                "The shifted matrix is skew Hermitian. Conjugating its determinant multiplies it by −1 in odd dimension, so the real part vanishes."),
            Helper("imaginaryShiftIntegral", "The imaginary determinant has integral coefficient", WithA(Imp(Call("Odd", V("d")),
                Ex("b", Z, Eqn(ImagDet, Mul(Call("Int.cast", V("b")), Call("Complex.I")))))),
                "Every entry of the imaginary shift is a Gaussian integer. Its determinant is a Gaussian integer with real part zero, and therefore equals bi for an integer b."),
            Helper("algebraicRatioRational", "The determinant quotient is rational", WithA(Imp(Call("Odd", V("d")),
                RationalValue(Ratio()))),
                "The real shift is an integral matrix. The imaginary-shift determinant divided by i is also an integer. Strict diagonal dominance makes both integers nonzero; their quotient supplies a nonzero rational."),
            Helper("algebraicSquareIdentity", "A quotient of quadratic determinants is a rational square", WithA(Imp(Call("Odd", V("d")),
                RationalSquare(QuadraticRatio()))),
                "Transposition identifies the determinants of dI+S and dI−S. Factoring d²I−S² gives the square of the first determinant. Factoring d²I+S² and using odd dimension gives the square of det(S+idI)/i. Thus the quotient is the square of the previously constructed rational. The theorem calH_closedForm identifies this quotient with d divided by the analytic Hessian determinant."),
            Helper("regularAlgebraicSquare", "The algebraic square for regular tournaments", WithA(Imp(Le(D(3), V("d")),
                Imp(Call("IsRegularTournament", V("A")), RationalSquare(QuadraticRatio())))),
                "Oddness of a regular tournament supplies the hypothesis of the quadratic determinant identity. The theorem calH_closedForm supplies the analytic identification, and regularLocalSolution supplies the required existence."),
            new DocumentBlock.Section(H("Matrix identities and inverse variations"), Blocks(BridgeInverseNodes())),
            Definition("inverseQ", "The diagonal resolvent",
                FiniteIndices(AAll(Eqn(Call("inverseQ", V("S"), V("y")),
                    Sub(Call("Matrix.diagonal", Lam("j", V("iota"), Fr(D(2), new Formula.Apply(V("y"), [V("j")])))), V("S"))),
                    ("S", GenericMatrix), ("y", GenericVector))),
                "The diagonal matrix with entries 2/y_j minus S."),
            Definition("alpha", "The inverse-entry sum",
                FiniteIndices(AAll(Eqn(Call("alpha", V("S"), V("y")),
                    SumOver("i", V("iota"), SumOver("j", V("iota"),
                        new Formula.Apply(Call("Inv.inv", Call("inverseQ", V("S"), V("y"))), [V("i"), V("j")])))),
                    ("S", GenericMatrix), ("y", GenericVector))),
                "The sum of all entries of the matrix inverse of inverseQ."))));

    private const string Prefix = "D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.";

    private static DocumentBlock.Describe Definition(string name, string title, Formula formula, string prose, bool literature = false) =>
        Describe.Lean(DescribeId.Create("wormald-" + name.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);


    private static DocumentBlock Helper(string name, string title, Formula statement, string prose) =>
        Describe.Lean(DescribeId.Create("wormald-" + name.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Z => Seq(Mathbb, Sp, Grp(V("Z")));

    private static Formula Skew => Call("Matrix.map", Call("skewAdjacency", V("A")), Call("Int.castRingHom", C));

    private static Formula Shift(Formula c) => Add(Skew, Smul(c, D(1)));

    private static Formula ImagDet => Call("Matrix.det", Shift(Mul(Call("Complex.I"), V("d"))));

    private static Formula Ratio() => Fr(Call("Matrix.det", Add(Smul(V("d"), D(1)), Skew)),
        Fr(ImagDet, Call("Complex.I")));

    private static Formula QuadraticRatio() => Fr(
        Call("Matrix.det", Sub(Smul(new Formula.Power(V("d"), D(2)), D(1)), Mul(Skew, Skew))),
        Call("Matrix.det", Add(Smul(new Formula.Power(V("d"), D(2)), D(1)), Mul(Skew, Skew))));

    private static Formula RationalValue(Formula value) => Ex("q", Q,
        And(Ne(V("q"), D(0)), Eqn(value, Call("Rat.cast", V("q")))));

    private static Formula RationalSquare(Formula value) => Ex("q", Q,
        And(Ne(V("q"), D(0)), Eqn(value, new Formula.Power(Call("Rat.cast", V("q")), D(2)))));

    private static Formula V(string name) => F.Id(name);

    private static Formula N => Seq(Mathbb, Sp, Grp(V("N")));

    private static Formula C => Seq(Mathbb, Sp, Grp(V("C")));

    private static Formula Q => Seq(Mathbb, Sp, Grp(V("Q")));

    private static Formula Index => Call("Fin", V("d"));

    private static Formula AType => new Formula.TypeArrow(Index, new Formula.TypeArrow(Index, V("Bool")));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula Ex(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);

    private static Formula WithA(Formula body) => All("d", N, All("A", AType, body));

    private static Formula Call(string name, params Formula[] args)
    {
        var parts = new List<Formula>();
        foreach (var word in name.Split('.'))
        {
            if (parts.Count > 0) parts.Add(Dot);
            parts.Add(V(word));
        }
        var head = Seq(Operatorname, Sp, Grp([.. parts]));
        return args.Length == 0 ? head : new Formula.Apply(head, [.. args]);
    }

    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);

    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);

    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);

    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));

    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));

    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);

    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);

    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);

    private static Formula Smul(Formula a, Formula b) => Seq(a, Cdot, Sp, Parenthesized(b));

    private static Formula Fr(Formula a, Formula b) => new Formula.Fraction(a, b);

    private static Formula Lam(string name, Formula type, Formula body) => Seq(Parenthesized(Seq(V(name), Colon, Sp, type, Mapsto, Sp, body)));

    private static Formula SumOver(string name, Formula type, Formula body) => Seq(new Formula.Subscript(Sum, Seq(V(name), Colon, Sp, type)), Sp, body);

    private static Formula GenericMatrix => Call("Matrix", V("iota"), V("iota"), C);

    private static Formula GenericVector => new Formula.TypeArrow(V("iota"), C);

    private static Formula FiniteIndices(Formula body) => All("iota", V("Type"),
        Instances(body, Call("Fintype", V("iota")), Call("DecidableEq", V("iota"))));

    private static Formula Det(Formula m) => Call("Matrix.det", m);

    private static Formula AAll(Formula body, params (string Name, Formula Type)[] variables)
    {
        for (var i = variables.Length - 1; i >= 0; --i)
            body = All(variables[i].Name, variables[i].Type, body);
        return body;
    }

    private static Formula AImps(Formula body, params Formula[] hypotheses)
    {
        for (var i = hypotheses.Length - 1; i >= 0; --i)
            body = Imp(hypotheses[i], body);
        return body;
    }

    private static Formula Instances(Formula body, params Formula[] instances)
    {
        var items = new List<Formula>();
        foreach (var instance in instances)
            items.AddRange([OpenBracket, instance, CloseBracket, Sp]);
        items.Add(body);
        return Seq([.. items]);
    }

    private static DocumentBlock[] BridgeInverseNodes()
    {
        Formula Pow(Formula a, byte n) => new Formula.Power(a, D(n));
        Formula Neg(Formula a) => Sub(D(0), a);
        Formula App(Formula a, params Formula[] args) => new Formula.Apply(a, [.. args]);
        Formula Inv(Formula a) => Call("Inv.inv", a);
        Formula Trans(Formula a) => Call("Matrix.transpose", a);
        Formula Single(Formula a) => Call("Pi.single", a, D(1));
        Formula Delta(Formula a, Formula b) => Call("ite", Eqn(a, b), D(1), D(0));
        Formula Const(Formula i, Formula a) => Call("Function.const", i, a);
        Formula Rows(Formula a, Formula index, Formula value) => All("i", index,
            Eqn(SumOver("l", index, App(a, V("i"), V("l"))), value));
        Formula Cols(Formula a, Formula index, Formula value) => All("j", index,
            Eqn(SumOver("l", index, App(a, V("l"), V("j"))), value));
        Formula Diff(Formula a, Formula i, Formula j, Formula last) =>
            Add(Sub(Sub(App(a, i, j), App(a, i, last)), App(a, last, j)), App(a, last, last));
        Formula D1(Formula f, Formula x, Formula v) => Call("fderiv", C, f, x, v);
        Formula D2(Formula f, Formula x, Formula v, Formula w) =>
            Call("fderiv", C, Lam("u", GenericVector, D1(f, V("u"), v)), x, w);
        Formula Fd(Formula f, Formula l, Formula x) => Call("HasFDerivAt", C, f, l, x);
        Formula Cd(Formula f, Formula x) => Call("ContDiffAt", C, D(2), f, x);
        Formula ClmComp(Formula a, Formula b) => Call("ContinuousLinearMap.comp", a, b);
        Formula MatrixMap(Formula index, Formula body) => Call("Matrix.of", Lam("i", index, Lam("k", index, body)));
        var idx = V("iota"); var mat = GenericMatrix; var vec = GenericVector;
        var i = V("i"); var j = V("j"); var k = V("k");
        var y = V("y"); var b = V("b"); var c = V("c"); var s = V("S"); var q = V("Q");
        var t = V("T"); var u = Call("bridgeU"); var size = Add(Call("Nat.cast", Call("Fintype.card", idx)), D(1));
        var sumIdx = Call("Sum", idx, V("Unit"));
        var sumMat = Call("Matrix", sumIdx, sumIdx, C);
        var lastSum = Call("Sum.inr", Call("Unit.unit"));
        var qMinus = Sub(Smul(c, D(1)), s);
        var quadPlus = Add(Smul(Pow(c, 2), D(1)), Mul(s, s));
        var quadMinus = Sub(Smul(Pow(c, 2), D(1)), Mul(s, s));
        var resT = Sub(D(1), Smul(c, Add(Inv(qMinus), Trans(Inv(qMinus)))));
        var qy = Call("inverseQ", s, y); var vy = Inv(qy); var af = Call("alpha", s);
        var invF = Lam("u", vec, Inv(Call("inverseQ", s, V("u"))));
        var qDeriv = Call("inverseQDeriv", y);
        var invDeriv = ClmComp(Neg(Call("ContinuousLinearMap.mulLeftRight", C, mat, vy, vy)), qDeriv);
        Formula Row(Formula a, Formula x) => SumOver("l", idx, App(a, x, V("l")));
        Formula Col(Formula a, Formula x) => SumOver("l", idx, App(a, V("l"), x));
        var yj = App(y, j); var yk = App(y, k);
        var goodY = All("i", idx, Ne(App(y, i), D(0)));
        var goodQ = Ne(Det(qy), D(0));
        var baseY = Const(idx, b); var baseQ = Call("inverseQ", s, baseY); var baseV = Inv(baseQ);
        var baseHypotheses = new Formula[] { Ne(b, D(0)), Ne(Det(baseQ), D(0)),
            Rows(baseV, idx, Fr(b, D(2))), Cols(baseV, idx, Fr(b, D(2))) };
        Formula Generic(Formula body, params (string Name, Formula Type)[] args) =>
            FiniteIndices(AAll(body, args));
        Formula AtY(Formula body, params (string Name, Formula Type)[] args) =>
            Generic(AImps(AAll(body, args), goodY, goodQ), ("S", mat), ("y", vec));
        Formula AtBase(Formula body, params (string Name, Formula Type)[] args) =>
            Generic(AImps(AAll(body, args), baseHypotheses), ("S", mat), ("b", C));
        var fin = Call("Fin", V("n")); var finSucc = Call("Fin", Add(V("n"), D(1)));
        var finMat = Call("Matrix", finSucc, finSucc, C);
        var finLast = Call("Fin.last", V("n"));
        var finMinor = MatrixMap(fin, Diff(t, Call("Fin.castSucc", i), Call("Fin.castSucc", k), finLast));
        var finSize = Add(Call("Nat.cast", V("n")), D(1));
        var secondAlpha = Add(
            Mul(Mul(Mul(Fr(Neg(D(4)), Pow(yj, 3)), Delta(k, j)), Row(vy, j)), Col(vy, j)),
            Mul(Fr(D(4), Mul(Pow(yj, 2), Pow(yk, 2))),
                Add(Mul(Mul(App(vy, j, k), Row(vy, k)), Col(vy, j)),
                    Mul(Mul(App(vy, k, j), Row(vy, j)), Col(vy, k)))));
        return
        [
            Helper("bridgeU_det", "The determinant of the difference-and-constant basis",
                Generic(Eqn(Det(u), size)),
                "The matrix with identity upper-left block, an all-one final column and an all-minus-one final row has determinant card(iota)+1, by its scalar Schur complement."),
            Helper("bridgeU_entry_left", "Difference-basis columns",
                Generic(Eqn(App(u, i, Call("Sum.inl", j)),
                    Sub(Delta(i, Call("Sum.inl", j)), Delta(i, lastSum))), ("i", sumIdx), ("j", idx)),
                "Each initial column is the corresponding coordinate vector minus the final coordinate vector."),
            Helper("bridgeU_entry_right", "The constant-basis column",
                Generic(Eqn(App(u, i, lastSum), D(1)), ("i", sumIdx)),
                "The final column of the basis matrix is the constant vector one."),
            Helper("bridgeU_congr", "The block diagonal congruence",
                Generic(AImps(Eqn(Mul(Mul(Trans(u), t), u), Call("Matrix.fromBlocks", Call("bridgeH", t),
                    D(0), D(0), MatrixMap(V("Unit"), Neg(size)))), Rows(t, sumIdx, Neg(D(1))), Cols(t, sumIdx, Neg(D(1)))), ("T", sumMat)),
                "If every row and column sums to minus one, congruence by the difference-and-constant basis has vanishing off-diagonal blocks, difference minor in the initial block and final entry minus (card(iota)+1)."),
            Helper("bridge_det", "The determinant of the difference minor",
                Generic(AImps(Eqn(Det(Call("bridgeH", t)), Mul(Neg(size), Det(t))),
                    Rows(t, sumIdx, Neg(D(1))), Cols(t, sumIdx, Neg(D(1)))), ("T", sumMat)),
                "Taking determinants of the block congruence and cancelling the nonzero basis determinant gives det(H)=−(card(iota)+1)det(T)."),
            Helper("skew_resolvent_det", "The determinant of the symmetric resolvent expression",
                Generic(AImps(Eqn(Det(resT), Fr(Neg(Det(quadPlus)), Det(quadMinus))),
                    Eqn(Trans(s), Neg(s)), Call("Odd", Call("Fintype.card", idx)), Ne(Det(qMinus), D(0))), ("S", mat), ("c", C)),
                "Multiplying T by (cI−S)(cI+S) gives −(c²I+S²). Transposition gives invertibility of both factors. Taking determinants in odd dimension yields the negative quadratic determinant quotient."),
            Helper("differenceMinor_det", "The finite-coordinate difference determinant",
                AAll(AImps(Eqn(Det(finMinor), Mul(Neg(finSize), Det(t))),
                    Rows(t, finSucc, Neg(D(1))), Cols(t, finSucc, Neg(D(1)))), ("n", N), ("T", finMat)),
                "Reindexing the difference-minor identity onto Fin(n+1) gives the determinant formula with multiplier −(n+1)."),
            Helper("inverse_row_sum", "Constant row sums of the inverse",
                Generic(AImps(Rows(Inv(q), idx, Inv(c)), Ne(c, D(0)), Ne(Det(q), D(0)), Rows(q, idx, c)), ("Q", mat), ("c", C)),
                "If Q maps the constant vector one to c times that vector, its inverse maps one to c inverse times one."),
            Helper("inverse_col_sum", "Constant column sums of the inverse",
                Generic(AImps(Cols(Inv(q), idx, Inv(c)), Ne(c, D(0)), Ne(Det(q), D(0)), Cols(q, idx, c)), ("Q", mat), ("c", C)),
                "Applying the row-sum identity to the transpose gives the corresponding column sums of the inverse."),
            Helper("resolvent_row_col_sum", "The resolvent expression has sums minus one",
                Generic(AImps(And(Rows(Sub(D(1), Smul(c, Add(Inv(q), Trans(Inv(q))))), idx, Neg(D(1))),
                    Cols(Sub(D(1), Smul(c, Add(Inv(q), Trans(Inv(q))))), idx, Neg(D(1)))),
                    Ne(c, D(0)), Ne(Det(q), D(0)), Rows(q, idx, c), Cols(q, idx, c)), ("Q", mat), ("c", C)),
                "The two inverse sums each contribute c inverse. Subtracting c times their sum from the identity leaves row and column sums equal to minus one."),
            Helper("skew_difference_det", "The determinant quotient for the difference minor",
                AAll(AImps(Eqn(Det(MatrixMap(fin, Diff(resT, Call("Fin.castSucc", i), Call("Fin.castSucc", k), finLast))),
                    Fr(Mul(finSize, Det(quadPlus)), Det(quadMinus))), Ne(c, D(0)), Eqn(Trans(s), Neg(s)),
                    Call("Odd", Add(V("n"), D(1))), Ne(Det(qMinus), D(0)), Rows(s, finSucc, D(0))),
                    ("n", N), ("S", finMat), ("c", C)),
                "Zero row sums of a skew matrix also give zero column sums. The resolvent expression therefore has sums minus one, and its difference-minor determinant is (n+1)det(c²I+S²)/det(c²I−S²)."),
            Helper("matrixInverse_hasFDerivAt", "Differentiating matrix inversion",
                Generic(Imp(Ne(Det(q), D(0)), Fd(Lam("M", mat, Inv(V("M"))),
                    Neg(Call("ContinuousLinearMap.mulLeftRight", C, mat, Inv(q), Inv(q))), q)), ("Q", mat)),
                "At an invertible complex matrix Q, the derivative of inversion maps H to −Q inverse H Q inverse. The matrix operator norm permits direct application of the normed-algebra inverse theorem."),
            Helper("inverseQ_hasFDerivAt", "Differentiating the diagonal resolvent",
                Generic(Imp(goodY, Fd(Call("inverseQ", s), qDeriv, y)), ("S", mat), ("y", vec)),
                "Each diagonal entry 2/y_j has derivative −2v_j/y_j². The off-diagonal skew matrix is constant."),
            Helper("inverse_hasFDerivAt", "Differentiating the inverse resolvent",
                AtY(Fd(invF, invDeriv, y)),
                "The chain rule composes the diagonal resolvent derivative with the derivative of matrix inversion."),
            Helper("alpha_hasFDerivAt", "Differentiating the inverse-entry sum",
                AtY(Fd(af, ClmComp(Call("sumEntriesCLM"), invDeriv), y)),
                "Summing all matrix entries is a continuous linear functional, so its composition with the inverse resolvent has the indicated derivative."),
            Helper("inverseQ_contDiffAt", "Smoothness of the diagonal resolvent",
                Generic(Imp(goodY, Cd(Call("inverseQ", s), y)), ("S", mat), ("y", vec)),
                "The nonzero coordinate hypothesis makes each reciprocal coordinate complex C2. Diagonal embedding and subtraction preserve this regularity."),
            Helper("inverse_contDiffAt", "Smoothness of the inverse resolvent",
                AtY(Cd(invF, y)),
                "Inversion is analytic on the units of a complex normed algebra. The nonzero determinant hypothesis allows composition with the C2 diagonal resolvent."),
            Helper("alpha_contDiffAt", "Smoothness of the scalar inverse-entry equation",
                AtY(Cd(af, y)),
                "The sum of inverse entries is complex C2 wherever all coordinates and the resolvent determinant are nonzero."),
            Helper("inverseQDeriv_single", "A single-coordinate diagonal derivative",
                Generic(Eqn(App(qDeriv, Single(j)), Smul(Fr(Neg(D(2)), Pow(yj, 2)),
                    Call("Matrix.diagonal", Single(j)))), ("y", vec), ("j", idx)),
                "Evaluating the diagonal resolvent derivative on a coordinate vector gives a diagonal matrix supported at that coordinate."),
            Helper("inverse_fderiv_single", "A single-coordinate inverse derivative",
                AtY(Eqn(D1(invF, y, Single(j)), Smul(Fr(D(2), Pow(yj, 2)),
                    MatrixMap(idx, Mul(App(vy, i, j), App(vy, j, k))))), ("j", idx)),
                "The jth partial derivative of the inverse matrix is 2/y_j² times the outer product of its jth column and jth row."),
            Helper("row_fderiv_single", "Differentiating an inverse row sum",
                AtY(Eqn(D1(Lam("u", vec, Row(Inv(Call("inverseQ", s, V("u"))), j)), y, Single(k)),
                    Mul(Mul(Fr(D(2), Pow(yk, 2)), App(vy, j, k)), Row(vy, k))), ("j", idx), ("k", idx)),
                "Summing the single-coordinate inverse derivative across a row gives 2V_jk/y_k² times the kth inverse row sum."),
            Helper("col_fderiv_single", "Differentiating an inverse column sum",
                AtY(Eqn(D1(Lam("u", vec, Col(Inv(Call("inverseQ", s, V("u"))), j)), y, Single(k)),
                    Mul(Mul(Fr(D(2), Pow(yk, 2)), App(vy, k, j)), Col(vy, k))), ("j", idx), ("k", idx)),
                "Summing the single-coordinate inverse derivative down a column gives 2V_kj/y_k² times the kth inverse column sum."),
            Helper("alpha_fderiv_single", "First partials of the scalar inverse-entry equation",
                AtY(Eqn(D1(af, y, Single(j)), Mul(Mul(Fr(D(2), Pow(yj, 2)), Row(vy, j)), Col(vy, j))), ("j", idx)),
                "The first partial is 2/y_j² times the product of the jth inverse row and column sums."),
            Helper("inverse_square_hasDerivAt", "The derivative of a reciprocal square",
                All("t", C, Imp(Ne(V("t"), D(0)), Call("HasDerivAt", C,
                    Lam("u", C, Fr(D(2), Pow(V("u"), 2))), Fr(Neg(D(4)), Pow(V("t"), 3)), V("t")))),
                "The scalar function 2/t² has derivative −4/t³ at every nonzero complex number."),
            Helper("alpha_second_single", "Second partials of the scalar inverse-entry equation",
                AtY(Eqn(D2(af, y, Single(j), Single(k)), secondAlpha), ("j", idx), ("k", idx)),
                "The first-partial formula holds on a neighbourhood where coordinates and determinant remain nonzero. Differentiating that equality uses the reciprocal-square derivative and the inverse row and column derivatives, producing the displayed second partial."),
            Helper("alpha_first_const", "Equal first partials at a balanced constant point",
                AtBase(Eqn(D1(af, baseY, Single(j)), Fr(D(1), D(2))), ("j", idx)),
                "When all coordinates equal b and every inverse row and column sums to b/2, every first partial equals one half."),
            Helper("alpha_second_const", "The second-partial matrix at a balanced constant point",
                AtBase(Eqn(D2(af, baseY, Single(j), Single(k)),
                    Sub(Mul(Inv(Pow(b, 2)), Add(App(baseV, j, k), App(baseV, k, j))),
                        Call("ite", Eqn(j, k), Inv(b), D(0)))), ("j", idx), ("k", idx)),
                "At the balanced constant point, the second-partial matrix is b inverse squared times V plus its transpose, minus b inverse times the identity.")
        ];
    }

}
