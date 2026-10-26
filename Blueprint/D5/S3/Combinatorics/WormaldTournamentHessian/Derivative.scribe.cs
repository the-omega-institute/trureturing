using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.WormaldTournamentHessian;

internal sealed class DerivativeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Regular tournament Hessians: derivative.",
        H("Tournament Hessian: derivative"), Blocks(
            Helper("polynomialSmooth", "Smoothness of the determinant polynomial", WithA(Call("ContDiff", C, D(2), Call("K", V("A")))),
                "The permutation expansion of the determinant expresses K as a finite sum of products of affine coordinate functions. It is complex C2 everywhere."),
            Helper("localSolutionOfInvertible", "A local solution from the implicit function theorem", WithA(Imp(Le(D(3), V("d")),
                Imp(Call("IsRegularTournament", V("A")), Imp(InvertibleLastDerivative,
                    Ex("h", HType, Call("IsLocalSolution", V("A"), V("h"))))))),
                "If the final-coordinate derivative at the expansion point is invertible, the complex implicit function theorem gives a C2 local solution. The zero value follows from the preceding determinant identity. This statement retains the invertibility hypothesis."),
            FirstAnalyticStage(),
            CofactorStage(),
            new DocumentBlock.Section(H("Second variations"), Blocks(AnalyticNodes())),
            Definition("appendLastLinear", "The continuous linear coordinate assembly",
                All("d", N, All("p", ProductDomain,
                    Eqn(new Formula.Apply(Call("appendLastLinear", V("d")), [V("p")]),
                        Call("appendLast", Call("Prod.fst", V("p")), Call("Prod.snd", V("p")))))),
                "The continuous complex linear map takes (y,t) to appendLast y t."))));

    private const string Prefix = "D5/S3/Combinatorics/WormaldTournamentHessian/Derivative.";

    private static DocumentBlock.Describe Definition(string name, string title, Formula formula, string prose, bool literature = false) =>
        Describe.Lean(DescribeId.Create("wormald-" + name.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);


    private static DocumentBlock Helper(string name, string title, Formula statement, string prose) =>
        Describe.Lean(DescribeId.Create("wormald-" + name.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Skew => Call("Matrix.map", Call("skewAdjacency", V("A")), Call("Int.castRingHom", C));

    private static Formula V(string name) => F.Id(name);

    private static Formula N => Seq(Mathbb, Sp, Grp(V("N")));

    private static Formula R => Seq(Mathbb, Sp, Grp(V("R")));

    private static Formula C => Seq(Mathbb, Sp, Grp(V("C")));

    private static Formula Index => Call("Fin", V("d"));

    private static Formula ShortIndex => Call("Fin", Call("Nat.sub", V("d"), D(1)));

    private static Formula FullVector => new Formula.TypeArrow(Index, C);

    private static Formula ShortVector => new Formula.TypeArrow(ShortIndex, C);

    private static Formula HType => new Formula.TypeArrow(ShortVector, C);

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

    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));

    private static Formula Iffn(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));

    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);

    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);

    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);

    private static Formula Smul(Formula a, Formula b) => Seq(a, Cdot, Sp, Parenthesized(b));

    private static Formula Fr(Formula a, Formula b) => new Formula.Fraction(a, b);

    private static Formula Lam(string name, Formula type, Formula body) => Seq(Parenthesized(Seq(V(name), Colon, Sp, type, Mapsto, Sp, body)));

    private static Formula SumOver(string name, Formula type, Formula body) => Seq(new Formula.Subscript(Sum, Seq(V(name), Colon, Sp, type)), Sp, body);

    private static Formula FullZVector => Call("Function.const", Index, Call("z", V("d")));

    private static Formula ProductDomain => Call("Prod", ShortVector, C);

    private static Formula ProductBase => Call("Prod.mk", ZVector, Call("z", V("d")));

    private static Formula UncurriedK => Lam("p", ProductDomain,
        Call("K", V("A"), Call("appendLast", Call("Prod.fst", V("p")), Call("Prod.snd", V("p")))));

    private static Formula InvertibleLastDerivative => Call("ContinuousLinearMap.IsInvertible",
        Call("ContinuousLinearMap.comp", Call("fderiv", C, UncurriedK, ProductBase),
            Call("ContinuousLinearMap.inr", C, ShortVector, C)));

    private static Formula ZVector => Call("Function.const", ShortIndex, Call("z", V("d")));

    private static DocumentBlock FirstAnalyticStage() => new DocumentBlock.Section(
        H("Coordinate derivatives and local existence"), Blocks(
            Helper("appendLastLinearApply", "Appending coordinates is complex linear",
                All("d", N, All("p", ProductDomain,
                    Eqn(new Formula.Apply(Call("appendLastLinear", V("d")), [V("p")]),
                        Call("appendLast", Call("Prod.fst", V("p")), Call("Prod.snd", V("p")))))),
                "The continuous complex linear map appendLastLinear appends the second component after the coordinates of the first component."),
            Helper("appendLast_update", "Changing the final coordinate",
                All("d", N, Imp(Le(D(1), V("d")), All("t", C,
                    Eqn(Call("appendLast", ZVector, V("t")),
                        Call("Function.update", FullZVector, Call("Fin.mk", Sub(V("d"), D(1))), V("t")))))),
                "For positive d, appending t to the constant vector replaces precisely the coordinate with natural value d minus one."),
            Helper("determinant_column_deriv", "Differentiating a single column",
                FiniteIndices(All("B", GenericMatrix, All("j", V("iota"),
                    All("u", GenericVector, All("v", GenericVector, All("t", C,
                        Call("HasDerivAt", Lam("s", C, Det(Call("Matrix.updateCol", V("B"), V("j"), Add(V("u"), Smul(V("s"), V("v")))))),
                            Det(Call("Matrix.updateCol", V("B"), V("j"), V("v"))), V("t")))))))),
                "Multilinearity makes the determinant affine in the scalar multiplying one column. Its derivative is the determinant with that column replaced by its direction."),
            Helper("K_coordinate_deriv", "A coordinate derivative of K",
                WithA(All("y", FullVector, All("j", Index, All("t", C,
                    Call("HasDerivAt", Lam("s", C, Call("K", V("A"), Call("Function.update", V("y"), V("j"), V("s")))),
                        new Formula.Negate(ColumnDet(V("y"), V("j"))), V("t")))))),
                "The derivative in coordinate j is minus the determinant obtained by replacing column j of the defining matrix by column j of one half I plus A. This holds at every y."),
            Helper("scalar_map_invertible", "Invertibility in one complex dimension",
                All("L", Call("ContinuousLinearMap", C, C, C),
                    Imp(Ne(new Formula.Apply(V("L"), [D(1)]), D(0)), Call("ContinuousLinearMap.IsInvertible", V("L")))),
                "A complex linear map on the scalar field multiplies by its value at one. The reciprocal scalar defines a continuous linear inverse when that value is nonzero."),
            Helper("scalar_partial_invertible", "A nonzero scalar partial derivative",
                ScalarPartialInvertibleFormula(),
                "Composing the full derivative with the inclusion of the scalar coordinate gives a complex linear map whose value at one is the scalar partial derivative."),
            Helper("det_rank_one_sub", "The rank-one determinant identity",
                All("d", N, All("Q", FullMatrix, Imp(Ne(Det(V("Q")), D(0)),
                    Eqn(Det(Sub(V("Q"), ConstantMatrix(D(1)))),
                        Mul(Det(V("Q")), Sub(D(1), SumEntries(Call("Inv.inv", V("Q"))))))))),
                "The matrix determinant lemma evaluates subtraction of the all-ones matrix. Its correction factor is one minus the sum of all entries of the inverse."),
            Helper("tournamentCoefficientIdentity", "Completeness and skew adjacency",
                WithA(Imp(Call("IsRegularTournament", V("A")),
                    Eqn(Smul(D(2), CoefficientMatrix), Add(ConstantMatrix(D(1)), Skew)))),
                "Tournament completeness gives twice the coefficient matrix as the sum of the all-ones matrix and the skew adjacency matrix."),
            Helper("K_resolvent_factorization", "A resolvent factorization of K",
                ResolventFactorizationFormula(),
                "When every coordinate and the resolvent determinant are nonzero, factor the defining matrix as the resolvent minus the all-ones matrix, followed by the diagonal matrix with entries y divided by two. The rank-one determinant identity then gives this formula."),
            Helper("K_eq_zero_iff_resolvent_sum", "The equation as an inverse-entry sum",
                WithA(Imp(Call("IsRegularTournament", V("A")), All("y", FullVector,
                    Imp(NonzeroCoordinates(V("y")), Imp(Ne(Det(Resolvent(V("y"))), D(0)),
                        Iffn(Eqn(Call("K", V("A"), V("y")), D(0)), Eqn(ResolventSum(V("y")), D(1)))))))),
                "The nonzero determinant and coordinate-product factors can be cancelled. Thus K vanishes exactly when the sum of all entries of the resolvent inverse equals one."),
            Helper("localSolution_resolvent_eq", "The inverse-entry equation near the base point",
                WithA(Imp(Le(D(3), V("d")), Imp(Call("IsRegularTournament", V("A")),
                    All("h", HType, Imp(Call("IsLocalSolution", V("A"), V("h")),
                        Imp(Ne(Det(Resolvent(FullZVector)), D(0)),
                            Call("Filter.Eventually", Lam("y", ShortVector,
                                Eqn(ResolventSum(Call("appendLast", V("y"), new Formula.Apply(V("h"), [V("y")]))), D(1))),
                                Call("nhds", ZVector)))))))),
                "Continuity keeps the coordinates and the resolvent determinant nonzero near the base point. Every C2 local solution therefore satisfies the inverse-entry equation on a neighbourhood."),
            Helper("regularLocalSolution", "Existence of the analytic local solution",
                WithA(Imp(Le(D(3), V("d")), Imp(Call("IsRegularTournament", V("A")),
                    Ex("h", HType, Call("IsLocalSolution", V("A"), V("h")))))),
                "The exact coordinate derivative is nonzero by strict diagonal dominance of the shifted skew adjacency matrix. Its scalar continuous linear derivative is invertible, so the complex implicit function theorem gives the required C2 local solution.")));

    private static Formula FullMatrix => Call("Matrix", Index, Index, C);

    private static Formula GenericMatrix => Call("Matrix", V("iota"), V("iota"), C);

    private static Formula GenericVector => new Formula.TypeArrow(V("iota"), C);

    private static Formula FiniteIndices(Formula body) => All("iota", V("Type"),
        Instances(body, Call("Fintype", V("iota")), Call("DecidableEq", V("iota"))));

    private static Formula Det(Formula m) => Call("Matrix.det", m);

    private static Formula CoefficientMatrix => Add(Smul(Fr(D(1), D(2)), D(1)),
        Call("Matrix.map", Call("adjacency", V("A")), Call("Int.castRingHom", C)));

    private static Formula ConstantMatrix(Formula c) => Call("Matrix.of", Lam("i", Index, Lam("j", Index, c)));

    private static Formula BaseMatrix(Formula y) => Sub(D(1), Mul(CoefficientMatrix, Call("Matrix.diagonal", y)));

    private static Formula ColumnDet(Formula y, Formula j) => Det(Call("Matrix.updateCol", BaseMatrix(y), j,
        Lam("i", Index, new Formula.Apply(CoefficientMatrix, [V("i"), j]))));

    private static Formula Resolvent(Formula y) => Sub(Call("Matrix.diagonal", Lam("j", Index,
        Fr(D(2), new Formula.Apply(y, [V("j")])))), Skew);

    private static Formula SumEntries(Formula m) => SumOver("i", Index, SumOver("j", Index,
        new Formula.Apply(m, [V("i"), V("j")])));

    private static Formula ResolventSum(Formula y) => SumEntries(Call("Inv.inv", Resolvent(y)));

    private static Formula NonzeroCoordinates(Formula y) => All("j", Index, Ne(new Formula.Apply(y, [V("j")]), D(0)));

    private static Formula ProductOver(string name, Formula type, Formula body) => Seq(
        new Formula.Subscript(Prod, Seq(V(name), Colon, Sp, type)), Sp, body);

    private static Formula ScalarPartialInvertibleFormula()
    {
        var pair = Call("Prod.mk", V("y"), V("t"));
        var scalarCurve = Lam("s", C, new Formula.Apply(V("F"), [Call("Prod.mk", V("y"), V("s"))]));
        var partialDerivative = Call("ContinuousLinearMap.comp",
            Call("fderiv", C, V("F"), pair),
            Call("ContinuousLinearMap.inr", C, V("E"), C));
        var statement = Imp(Call("DifferentiableAt", C, V("F"), pair),
            Imp(Call("HasDerivAt", scalarCurve, V("c"), V("t")),
                Imp(Ne(V("c"), D(0)), Call("ContinuousLinearMap.IsInvertible", partialDerivative))));
        statement = All("c", C, statement);
        statement = All("t", C, statement);
        statement = All("y", V("E"), statement);
        statement = All("F", new Formula.TypeArrow(Call("Prod", V("E"), C), C), statement);
        statement = Instances(statement, Call("NormedAddCommGroup", V("E")), Call("NormedSpace", C, V("E")));
        return All("E", V("Type"), statement);
    }

    private static Formula ResolventFactorizationFormula()
    {
        var value = Mul(Mul(Det(Resolvent(V("y"))), Sub(D(1), ResolventSum(V("y")))),
            ProductOver("j", Index, Fr(new Formula.Apply(V("y"), [V("j")]), D(2))));
        var statement = Eqn(Call("K", V("A"), V("y")), value);
        statement = Imp(Ne(Det(Resolvent(V("y"))), D(0)), statement);
        statement = Imp(NonzeroCoordinates(V("y")), statement);
        statement = All("y", FullVector, statement);
        return WithA(Imp(Call("IsRegularTournament", V("A")), statement));
    }

    private static DocumentBlock CofactorStage() => new DocumentBlock.Section(
        H("Cofactors and the nonzero coordinate derivative"), Blocks(
            Helper("det_const_perturb", "The determinant of a constant perturbation", CofactorConstantFormula(),
                "The matrix determinant lemma reduces a constant perturbation of the identity to one scalar. The determinant is one plus the sum of the constant diagonal contributions."),
            Helper("det_projection_update", "A column replacement in the constant-vector projection", CofactorProjectionFormula(),
                "Let P=I−J/(n+1), where every entry of J is one. Replacing column l by v gives determinant equal to the sum of the coordinates of v divided by n+1. Summing the rows and expanding the resulting sparse row leaves a principal minor with determinant 1/(n+1)."),
            Helper("det_doubly_stochastic_cofactor", "A cofactor of a centered doubly stochastic matrix", CofactorStochasticFormula(),
                "An invertible complex matrix whose rows and columns sum to one factors its centered matrix as A(I−J/(n+1)). The inverse image of the lth coordinate vector has coordinate sum one. The projection column formula therefore gives det A divided by n+1."),
            Helper("cofactor_eq_of_zero_sums", "A cofactor of a matrix with zero row and column sums", CofactorZeroSumFormula(),
                "Adding J/(n+1) to B changes every row and column sum from zero to one. If the resulting determinant is nonzero, each diagonal cofactor of B equals that determinant divided by n+1."),
            Helper("regularColumnSlopeValue", "The common first-coordinate determinant coefficient", CofactorTournamentFormula(),
                "Put C=½I+A and B=I−CD_z. Regularity gives zero row and column sums for B and the factorization B+J/d=(dI−S)/d. Every determinant obtained by replacing column l of B with column l of C equals det(dI−S)/(2d^d), independently of l. The coordinate derivative of K is the negative of this column replacement determinant."),
            Helper("regularSkewRowSum", "Regular skew adjacency has zero row sums", WithA(Imp(Le(D(3), V("d")),
                Imp(Call("IsRegularTournament", V("A")), All("i", Index,
                    Eqn(SumOver("j", Index, CofactorEntry(Skew, V("i"), V("j"))), D(0)))))),
                "Pair completeness and constant out-degree imply the same in-degree at every vertex. Subtracting the transpose therefore gives zero in every skew adjacency row sum."),
            Helper("regularSkewColSum", "Regular skew adjacency has zero column sums", WithA(Imp(Le(D(3), V("d")),
                Imp(Call("IsRegularTournament", V("A")), All("j", Index,
                    Eqn(SumOver("i", Index, CofactorEntry(Skew, V("i"), V("j"))), D(0)))))),
                "Skew symmetry identifies each column sum with the negative of the corresponding row sum. The zero row sums thus give zero column sums as well."),
            Helper("shiftedNegativeDetNeZero", "The negative skew shift is nonsingular", WithA(
                Ne(Call("Matrix.det", Sub(Smul(Call("Nat.cast", V("d")), D(1)), Skew)), D(0))),
                "The matrix dI−S is the transpose of S+dI. Its determinant equals the nonzero determinant furnished by strict diagonal dominance. This assertion does not require tournament regularity.")));

    private static Formula CofactorGenericIndex => Call("Fin", Add(V("n"), D(1)));

    private static Formula CofactorGenericSize => Add(Call("Nat.cast", V("n")), D(1));

    private static Formula CofactorMatrixType(Formula index) => Call("Matrix", index, index, C);

    private static Formula CofactorVectorType(Formula index) => new Formula.TypeArrow(index, C);

    private static Formula CofactorEntry(Formula matrix, Formula row, Formula column) =>
        new Formula.Apply(matrix, [row, column]);

    private static Formula CofactorConstant(Formula index, Formula value) =>
        Call("Matrix.of", Lam("i", index, Lam("j", index, value)));

    private static Formula CofactorUniform => CofactorConstant(CofactorGenericIndex,
        Fr(D(1), CofactorGenericSize));

    private static Formula CofactorColumn(Formula matrix, Formula index) =>
        Lam("i", index, CofactorEntry(matrix, V("i"), V("l")));

    private static Formula CofactorCoordinate => Call("Pi.single", V("l"), D(1));

    private static Formula CofactorRowSums(Formula matrix, Formula index, Formula value) =>
        All("i", index, Eqn(SumOver("j", index, CofactorEntry(matrix, V("i"), V("j"))), value));

    private static Formula CofactorColumnSums(Formula matrix, Formula index, Formula value) =>
        All("j", index, Eqn(SumOver("i", index, CofactorEntry(matrix, V("i"), V("j"))), value));

    private static Formula CofactorConstantFormula() => All("n", N, All("c", C,
        Eqn(Call("Matrix.det", Add(D(1), CofactorConstant(Call("Fin", V("n")), V("c")))),
            Add(D(1), Mul(Call("Nat.cast", V("n")), V("c"))))));

    private static Formula CofactorProjectionFormula() => All("n", N,
        All("l", CofactorGenericIndex, All("v", CofactorVectorType(CofactorGenericIndex),
            Eqn(Call("Matrix.det", Call("Matrix.updateCol", Sub(D(1), CofactorUniform), V("l"), V("v"))),
                Fr(SumOver("i", CofactorGenericIndex, new Formula.Apply(V("v"), [V("i")])),
                    CofactorGenericSize)))));

    private static Formula CofactorStochasticFormula() => All("n", N,
        All("l", CofactorGenericIndex, All("A", CofactorMatrixType(CofactorGenericIndex),
            Imp(Ne(Call("Matrix.det", V("A")), D(0)),
                Imp(CofactorRowSums(V("A"), CofactorGenericIndex, D(1)),
                    Imp(CofactorColumnSums(V("A"), CofactorGenericIndex, D(1)),
                        Eqn(Call("Matrix.det", Call("Matrix.updateCol", Sub(V("A"), CofactorUniform),
                                V("l"), CofactorCoordinate)),
                            Fr(Call("Matrix.det", V("A")), CofactorGenericSize))))))));

    private static Formula CofactorZeroSumFormula() => All("n", N,
        All("l", CofactorGenericIndex, All("B", CofactorMatrixType(CofactorGenericIndex),
            Imp(Ne(Call("Matrix.det", Add(V("B"), CofactorUniform)), D(0)),
                Imp(CofactorRowSums(V("B"), CofactorGenericIndex, D(0)),
                    Imp(CofactorColumnSums(V("B"), CofactorGenericIndex, D(0)),
                        Eqn(Call("Matrix.det", Call("Matrix.updateCol", V("B"), V("l"), CofactorCoordinate)),
                            Fr(Call("Matrix.det", Add(V("B"), CofactorUniform)), CofactorGenericSize))))))));

    private static Formula CofactorTournamentC => Add(Smul(Fr(D(1), D(2)), D(1)),
        Call("Matrix.map", Call("adjacency", V("A")), Call("Int.castRingHom", C)));

    private static Formula CofactorTournamentB => Sub(D(1),
        Mul(CofactorTournamentC, Call("Matrix.diagonal", FullZVector)));

    private static Formula CofactorTournamentFormula() => WithA(Imp(Le(D(3), V("d")),
        Imp(Call("IsRegularTournament", V("A")), All("l", Index,
            Eqn(Call("Matrix.det", Call("Matrix.updateCol", CofactorTournamentB, V("l"),
                    CofactorColumn(CofactorTournamentC, Index))),
                Fr(Call("Matrix.det", Sub(Smul(Call("Nat.cast", V("d")), D(1)), Skew)),
                    Mul(D(2), new Formula.Power(Call("Nat.cast", V("d")), V("d")))))))));

    private static DocumentBlock[] AnalyticNodes()
    {
        var field = V("kappa");
        var e = V("E");
        var fspace = V("F");
        var gspace = V("G");
        var shortN = new Formula.TypeArrow(Call("Fin", V("n")), C);
        var realN = new Formula.TypeArrow(Call("Fin", V("n")), R);
        Formula Arr(Formula a, Formula b) => new Formula.TypeArrow(a, b);
        Formula App(string name, params Formula[] args) => new Formula.Apply(V(name), [.. args]);
        Formula Pair(Formula a, Formula b) => Call("Prod.mk", a, b);
        Formula Cd(Formula k, Formula f, Formula x) => Call("ContDiffAt", k, D(2), f, x);
        Formula D1(Formula k, Formula f, Formula x, Formula v) => Call("fderiv", k, f, x, v);
        Formula D2(Formula k, Formula f, Formula x, Formula v, Formula w) => Call("second", k, f, x, v, w);

        Formula Single(Formula j) => Call("Pi.single", j, D(1));
        Formula Neg(Formula a) => Sub(D(0), a);

        Formula Const(Formula index, Formula a) => Call("Function.const", index, a);
        Formula Delta(Formula j, Formula k) => Call("ite", Eqn(j, k), D(1), D(0));
        Formula Germ(Formula f, Formula value, Formula domain, Formula x) =>
            Call("Filter.EventuallyEq", Call("nhds", x), f, Lam("y", domain, value));

        Formula C2(Formula f, Formula x) => Cd(C, f, x);
        var x = V("x");
        var v = V("v");
        var w = V("w");
        var ff = V("f");
        var gg = V("g");
        var hh = V("h");
        var j = V("j");
        var k = V("k");
        var a = V("a");
        var nIndex = Call("Fin", V("n"));
        var constantA = Const(nIndex, a);
        var h0 = App("h", constantA);
        var dhj = D1(C, hh, constantA, Single(j));
        var dhk = D1(C, hh, constantA, Single(k));
        var nVectors = new (string, Formula)[] { ("n", N), ("f", Arr(shortN, C)), ("x", shortN) };
        var nH = new (string, Formula)[] { ("n", N), ("a", C), ("h", Arr(shortN, C)) };
        var allNvw = new (string, Formula)[] { ("v", shortN), ("w", shortN) };
        var allNjk = new (string, Formula)[] { ("j", nIndex), ("k", nIndex) };

        Formula Joint(bool coordinates)
        {
            var ltype = Call("ContinuousLinearMap", C, ProductDomain, FullVector);
            var p = App("L", ProductBase);
            var alph = V("alpha");
            var graph = Lam("y", ShortVector, App("alpha", App("L", Pair(V("y"), App("h", V("y"))))));
            var tangentJ = App("L", Pair(Single(j), Neg(D(1))));
            var tangentK = App("L", Pair(Single(k), Neg(D(1))));
            var ci = V("c");
            var hypotheses = new List<Formula> {
                Le(D(3), V("d")), Call("IsLocalSolution", V("A"), hh), C2(alph, p),
                Germ(graph, D(1), ShortVector, ZVector), Ne(ci, D(0))
            };
            Formula secondValue;
            var bindings = new List<(string, Formula)> { ("h", HType), ("L", ltype), ("alpha", Arr(FullVector, C)), ("c", C) };
            if (coordinates)
            {
                var iota = V("iota");
                var last = V("last");
                var matrix = V("M");
                bindings.Add(("iota", Arr(ShortIndex, Index)));
                bindings.Add(("last", Index));
                bindings.Add(("M", Call("Matrix", Index, Index, C)));
                hypotheses.Add(All("j", ShortIndex, Eqn(App("L", Pair(Single(j), D(0))), Single(App("iota", j)))));
                hypotheses.Add(Eqn(App("L", Pair(D(0), D(1))), Single(last)));
                hypotheses.Add(All("i", Index, Eqn(D1(C, alph, p, Single(V("i"))), ci)));
                hypotheses.Add(AAll(Eqn(D2(C, alph, p, Single(V("i")), Single(V("l"))), App("M", V("i"), V("l"))), ("i", Index), ("l", Index)));
                secondValue = Add(Sub(Sub(App("M", App("iota", j), App("iota", k)),
                    App("M", App("iota", j), last)), App("M", last, App("iota", k))), App("M", last, last));
            }
            else
            {
                hypotheses.Add(All("j", ShortIndex, Eqn(D1(C, alph, p, App("L", Pair(Single(j), D(0)))), ci)));
                hypotheses.Add(Eqn(D1(C, alph, p, App("L", Pair(D(0), D(1)))), ci));
                secondValue = D2(C, alph, p, tangentJ, tangentK);
            }
            var conclusion = AAll(Eqn(Call("hessian", hh, j, k),
                Add(Add(D(1), Delta(j, k)), Mul(Fr(Call("z", V("d")), ci), secondValue))),
                ("j", ShortIndex), ("k", ShortIndex));
            return WithA(AAll(AImps(conclusion, [.. hypotheses]), [.. bindings]));
        }
        return [
            AnalyticHelper("hessian_of_implicit_scalar", "The Hessian from a scalar implicit equation", Joint(false),
                "If a C2 scalar equation has a constant nonzero first partial c in every appended coordinate and is constant along the graph of h, then h_j=-1. The second implicit derivative and the angular formula give H_jk=1+delta_jk+(z/c) D2alpha(L(e_j,-1),L(e_k,-1))."),
            AnalyticHelper("hessian_of_implicit_coordinates", "The Hessian from the coordinate derivatives of the scalar equation", Joint(true),
                "If M is the matrix of second complex partial derivatives of the scalar equation, the graph tangent vectors are coordinate differences. Bilinearity gives the four-entry difference M_jk-M_jd-M_dk+M_dd in the angular Hessian formula.")
        ];
    }

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

    private static DocumentBlock AnalyticHelper(string name, string title, Formula statement, string prose) =>
        Describe.Lean(DescribeId.Create("wormald-analytic-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

}
