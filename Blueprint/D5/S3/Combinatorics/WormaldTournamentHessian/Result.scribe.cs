using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.WormaldTournamentHessian;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/WormaldTournamentHessian/Result.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/wormald2026tournaments");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The determinant polynomial and analytic Hessian of a regular tournament.",
        H("Wormald's tournament Hessian"), Blocks(
            Definition("IsRegularTournament", "Regular tournaments", RegularFormula(),
                "The adjacency is Boolean. Each diagonal entry is false, and for distinct vertices exactly one direction is true. The out-degree is the same natural number at every vertex. No oddness hypothesis is added."),
            Definition("adjacency", "The integral adjacency matrix", WithA(All("i", Index, All("j", Index,
                Eqn(Call("adjacency", V("A"), V("i"), V("j")), Indicator(V("i"), V("j")))))),
                "True edges have integral entry one and false edges have integral entry zero."),
            Definition("skewAdjacency", "The skew adjacency matrix", WithA(Eqn(Call("skewAdjacency", V("A")),
                Sub(Call("adjacency", V("A")), Call("Matrix.transpose", Call("adjacency", V("A")))))),
                "The integral matrix S is A minus its transpose. It has zero diagonal and entries in {−1,0,1}."),
            Definition("z", "The expansion point", All("d", N, Eqn(Call("z", V("d")), Fr(D(2), V("d")))),
                "The source defines z=2/d and the constant vector with this coordinate. Only d at least three enters the conjecture."),
            Definition("K", "The determinant polynomial", WithA(All("y", FullVector,
                Eqn(Call("K", V("A"), V("y")), Call("Matrix.det", Sub(D(1),
                    Mul(Add(Smul(Fr(D(1), D(2)), D(1)), Call("Matrix.map", Call("adjacency", V("A")),
                        Call("Int.castRingHom", C))), Call("Matrix.diagonal", V("y")))))))),
                "Section 1 defines B=I−(½I+A)Dᵧ and K(y)=det B. The map Int.castRingHom embeds the integral adjacency into the complex numbers. Matrix multiplication retains the source's column scaling by y."),
            Definition("appendLast", "The final implicit coordinate", AppendFormula(),
                "Fin.snoc appends the scalar after the first d−1 coordinates. The index is lifted by its natural value to Fin((d−1)+1); for d positive this is the order-preserving identification with Fin d. The case d=0 has no indices."),
            Definition("IsLocalSolution", "A complex C2 local solution", LocalFormula(),
                "Section 1: “one may solve K(y)=0 in the neighbourhood of z and obtain y_d=h(y_1,…,y_{d−1})”. The definition specifies h(z′)=z, ContDiffAt over the complex scalar field of order two, and an equation holding eventually in the neighbourhood filter at z′. It imposes no global equation on h."),
            Definition("phase", "Real angular coordinates", PhaseFormula(),
                "Section 1 defines f̃(θ)=log h(ze^{iθ₁},…,ze^{iθ_{d−1}}). Complex.log is the principal logarithm. Its argument at zero is the positive real number z when h is a local solution and d is at least three."),
            Definition("hessian", "The real angular Hessian", HessianFormula(),
                "The entry in row j and column k differentiates θ↦fderiv ℝ (phase h) θ (Pi.single j 1) once more over ℝ in the direction Pi.single k 1, at θ=0. Thus the definition uses fderiv of fderiv and keeps the complex-valued output."),
            Definition("calH", "The Hessian determinant", WithH(Eqn(Call("calH", V("h")), Call("Matrix.det", Call("hessian", V("h"))))),
                "Section 1 lets “H denote the determinant of the Hessian … of f̃ at θ_j=0”. The determinant has d−1 rows and columns."),
            Definition("claim", "Conjecture 6 with local existence", Eqn(V("claim"), ClaimFormula()),
                "The supplied source excerpt does not identify a printed page number. The formula includes existence of a complex C2 local solution and the same conclusion for every such solution. The rational is embedded into ℂ before squaring. The theorem result proves this full statement with the stated analytic definitions."),
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
            Helper("regularDegree", "The degree and order identity", WithA(Imp(Le(D(3), V("d")),
                Imp(Call("IsRegularTournament", V("A")), Ex("r", N,
                    And(Eqn(V("d"), Add(Mul(D(2), V("r")), D(1))),
                        All("i", Index, Eqn(SumOver("j", Index, Call("adjacency", V("A"), V("i"), V("j"))), Call("Nat.cast", V("r"))))))))),
                "If the common out-degree is r, counting both orientations gives 2dr=d(d−1). Positivity of d gives d=2r+1, and every integral adjacency row sums to r."),
            Helper("regularOdd", "Regular tournaments have odd order", WithA(Imp(Le(D(3), V("d")),
                Imp(Call("IsRegularTournament", V("A")), Call("Odd", V("d"))))),
                "If every out-degree is r, summing the two orientations of each off-diagonal pair gives 2dr=d(d−1). Since d is positive, d=2r+1."),
            Helper("algebraicSquareIdentity", "A quotient of quadratic determinants is a rational square", WithA(Imp(Call("Odd", V("d")),
                RationalSquare(QuadraticRatio()))),
                "Transposition identifies the determinants of dI+S and dI−S. Factoring d²I−S² gives the square of the first determinant. Factoring d²I+S² and using odd dimension gives the square of det(S+idI)/i. Thus the quotient is the square of the previously constructed rational. The theorem calH_closedForm identifies this quotient with d divided by the analytic Hessian determinant."),
            Helper("regularAlgebraicSquare", "The algebraic square for regular tournaments", WithA(Imp(Le(D(3), V("d")),
                Imp(Call("IsRegularTournament", V("A")), RationalSquare(QuadraticRatio())))),
                "Oddness of a regular tournament supplies the hypothesis of the quadratic determinant identity. The theorem calH_closedForm supplies the analytic identification, and regularLocalSolution supplies the required existence."),
            Helper("determinantAtBase", "The determinant vanishes at the expansion point", WithA(Imp(Le(D(3), V("d")),
                Imp(Call("IsRegularTournament", V("A")), Eqn(Call("K", V("A"), FullZVector), D(0))))),
                "The constant vector one is in the kernel of I−(½I+A)D_z: each row of ½I+A sums to d/2. Hence its determinant is zero."),
            Helper("polynomialSmooth", "Smoothness of the determinant polynomial", WithA(Call("ContDiff", C, D(2), Call("K", V("A")))),
                "The permutation expansion of the determinant expresses K as a finite sum of products of affine coordinate functions. It is complex C2 everywhere."),
            Helper("localSolutionOfInvertible", "A local solution from the implicit function theorem", WithA(Imp(Le(D(3), V("d")),
                Imp(Call("IsRegularTournament", V("A")), Imp(InvertibleLastDerivative,
                    Ex("h", HType, Call("IsLocalSolution", V("A"), V("h"))))))),
                "If the final-coordinate derivative at the expansion point is invertible, the complex implicit function theorem gives a C2 local solution. The zero value follows from the preceding determinant identity. This statement retains the invertibility hypothesis."),
            FirstAnalyticStage(), CofactorStage(),
            new DocumentBlock.Section(H("Second derivatives of implicit phases"), Blocks(AnalyticNodes())),
            new DocumentBlock.Section(H("Matrix inverses and determinant bridges"), Blocks(BridgeInverseNodes())), HessianResolution())));

    private static DocumentBlock.Describe Definition(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("wormald-" + name.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            DefinitionContent(name, prose), DescribeRole.Definition);

    private static BlockSequence DefinitionContent(string name, string prose) => name == "claim"
        ? Blocks(Paragraph(Text("Section 1: “Conjecture 6. For every regular tournament "),
            Math(new Formula.Power(V("T"), Star)), Text(" on at least three vertices, "),
            Math(Ne(Seq(Mathcal, Sp, Grp(V("H"))), D(0))), Text(" and "),
            Math(Fr(V("d"), Seq(Mathcal, Sp, Grp(V("H"))))),
            Text(" is the square of a rational.”")), Paragraph(Text(prose)))
        : Blocks(Paragraph(Text(prose)));

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
    private static Formula R => Seq(Mathbb, Sp, Grp(V("R")));
    private static Formula C => Seq(Mathbb, Sp, Grp(V("C")));
    private static Formula Q => Seq(Mathbb, Sp, Grp(V("Q")));
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
    private static Formula WithH(Formula body) => All("d", N, All("h", HType, body));
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
    private static Formula Iffn(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Smul(Formula a, Formula b) => Seq(a, Cdot, Sp, Parenthesized(b));
    private static Formula Fr(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Lam(string name, Formula type, Formula body) => Seq(Parenthesized(Seq(V(name), Colon, Sp, type, Mapsto, Sp, body)));
    private static Formula Entry(Formula i, Formula j) => new Formula.Apply(V("A"), [i, j]);
    private static Formula Indicator(Formula i, Formula j) => Call("ite", Eqn(Entry(i, j), V("true")), D(1), D(0));
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
    private static Formula RegularFormula() => WithA(Eqn(Call("IsRegularTournament", V("A")),
        And(All("i", Index, Eqn(Entry(V("i"), V("i")), V("false"))),
            And(All("i", Index, All("j", Index, Imp(Ne(V("i"), V("j")), Iffn(Eqn(Entry(V("i"), V("j")), V("true")), Eqn(Entry(V("j"), V("i")), V("false")))))),
                Ex("r", N, All("i", Index, Eqn(SumOver("j", Index, Indicator(V("i"), V("j"))), V("r"))))))));
    private static Formula AppendFormula() => All("d", N, All("y", ShortVector, All("t", C, All("i", Index,
        Eqn(Call("appendLast", V("y"), V("t"), V("i")),
            Call("Fin.snoc", V("y"), V("t"), Call("Fin.ofNat", Add(Call("Nat.sub", V("d"), D(1)), D(1)), Call("Fin.val", V("i")))))))));
    private static Formula LocalFormula() => WithA(All("h", HType, Eqn(Call("IsLocalSolution", V("A"), V("h")),
        And(Eqn(new Formula.Apply(V("h"), [ZVector]), Call("z", V("d"))),
            And(Call("ContDiffAt", C, D(2), V("h"), ZVector),
                Call("Filter.Eventually", Lam("y", ShortVector, Eqn(Call("K", V("A"), Call("appendLast", V("y"), new Formula.Apply(V("h"), [V("y")]))), D(0))),
                    Call("nhds", ZVector)))))));
    private static Formula PhaseFormula() => WithH(All("theta", new Formula.TypeArrow(ShortIndex, R),
        Eqn(Call("phase", V("h"), V("theta")), Call("Complex.log", new Formula.Apply(V("h"), [
            Lam("j", ShortIndex, Mul(Call("z", V("d")), Call("Complex.exp", Mul(Call("Complex.I"), new Formula.Apply(V("theta"), [V("j")])))))])))));
    private static Formula HessianFormula() => WithH(All("j", ShortIndex, All("k", ShortIndex,
        Eqn(Call("hessian", V("h"), V("j"), V("k")),
            Call("fderiv", R, Lam("theta", new Formula.TypeArrow(ShortIndex, R),
                Call("fderiv", R, Call("phase", V("h")), V("theta"), Call("Pi.single", V("j"), D(1)))),
                D(0), Call("Pi.single", V("k"), D(1)))))));
    private static Formula ClaimFormula() => All("d", N, Imp(Le(D(3), V("d")), All("A", AType,
        Imp(Call("IsRegularTournament", V("A")), And(Ex("h", HType, Call("IsLocalSolution", V("A"), V("h"))),
            All("h", HType, Imp(Call("IsLocalSolution", V("A"), V("h")),
                And(Ne(Call("calH", V("h")), D(0)), Ex("q", Q,
                    Eqn(Fr(V("d"), Call("calH", V("h"))), new Formula.Power(Call("Rat.cast", V("q")), D(2))))))))))));
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
        All("finite", Call("Fintype", V("iota")), All("decidable", Call("DecidableEq", V("iota")), body)));
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
        statement = All("space", Call("NormedSpace", C, V("E")), statement);
        statement = All("group", Call("NormedAddCommGroup", V("E")), statement);
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
        Formula Compose(Formula g, Formula f) => Call("Function.comp", g, f);
        Formula Single(Formula j) => Call("Pi.single", j, D(1));
        Formula Neg(Formula a) => Sub(D(0), a);
        Formula Sq(Formula a) => new Formula.Power(a, D(2));
        Formula Const(Formula index, Formula a) => Call("Function.const", index, a);
        Formula Delta(Formula j, Formula k) => Call("ite", Eqn(j, k), D(1), D(0));
        Formula Germ(Formula f, Formula value, Formula domain, Formula x) =>
            Call("Filter.EventuallyEq", Call("nhds", x), f, Lam("y", domain, value));
        Formula Member(Formula value) => Call("Membership.mem", value, Call("Complex.slitPlane"));
        Formula LogPhase(Formula a, Formula h) => Call("logarithmicPhase", a, h);
        Formula Chart(Formula a) => Call("exponentialChart", a);
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

        Formula Implicit(bool scalar, bool twice)
        {
            var outputH = scalar ? field : fspace;
            var outputF = scalar ? field : gspace;
            var product = Call("Prod", e, outputH);
            var graph = Lam("y", e, Pair(V("y"), App("h", V("y"))));
            var basePoint = Pair(x, App("h", x));
            var tangentV = Pair(v, D1(field, hh, x, v));
            var tangentW = Pair(w, D1(field, hh, x, w));
            var final = D1(field, V("F0"), basePoint, Pair(D(0), D(1)));
            Formula conclusion = scalar
                ? twice
                    ? Eqn(D2(field, hh, x, v, w), Fr(Neg(D2(field, V("F0"), basePoint, tangentV, tangentW)), final))
                    : Eqn(D1(field, hh, x, v), Fr(Neg(D1(field, V("F0"), basePoint, Pair(v, D(0)))), final))
                : twice
                    ? Eqn(Add(D2(field, V("F0"), basePoint, tangentV, tangentW),
                        D1(field, V("F0"), basePoint, Pair(D(0), D2(field, hh, x, v, w)))), D(0))
                    : Eqn(D1(field, V("F0"), basePoint, tangentV), D(0));
            conclusion = AAll(conclusion, twice ? [("v", e), ("w", e)] : [("v", e)]);
            var hypotheses = new List<Formula> {
                Cd(field, hh, x), Cd(field, V("F0"), basePoint),
                Germ(Compose(V("F0"), graph), D(0), e, x)
            };
            if (scalar) hypotheses.Add(Ne(final, D(0)));
            return ANormed(AAll(AImps(conclusion, [.. hypotheses]),
                ("h", Arr(e, outputH)), ("F0", Arr(product, outputF)), ("x", e)),
                scalar ? ["E"] : ["E", "F", "G"]);
        }

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
            AnalyticHelper("second_comp", "The second derivative of a composition",
                ANormed(AAll(AImps(Eqn(D2(field, Compose(gg, ff), x, v, w),
                    Add(D2(field, gg, App("f", x), D1(field, ff, x, v), D1(field, ff, x, w)),
                        D1(field, gg, App("f", x), D2(field, ff, x, v, w)))),
                    Cd(field, ff, x), Cd(field, gg, App("f", x))),
                    ("f", Arr(e, fspace)), ("g", Arr(fspace, gspace)), ("x", e), ("v", e), ("w", e)), "E", "F", "G"),
                "Write second(f,x,v,w) for the derivative in direction w of y mapped to Df(y)v. The chain rule gives the outer second derivative on the two inner velocities, plus the outer first derivative on the inner acceleration."),
            AnalyticHelper("second_eq_zero_of_eventually", "A zero germ has zero second derivative",
                ANormed(AAll(Imp(Germ(ff, D(0), e, x), Eqn(D2(field, ff, x, v, w), D(0))),
                    ("f", Arr(e, fspace)), ("x", e), ("v", e), ("w", e)), "E", "F"),
                "A function agreeing with zero on a neighbourhood has the same first and second Frechet derivatives as zero. No separate smoothness hypothesis is needed for this germ equality."),
            AnalyticHelper("second_graph", "The second derivative of a graph",
                ANormed(AAll(Imp(Cd(field, hh, x), Eqn(D2(field,
                    Lam("y", e, Pair(V("y"), App("h", V("y")))), x, v, w), Pair(D(0), D2(field, hh, x, v, w)))),
                    ("h", Arr(e, fspace)), ("x", e), ("v", e), ("w", e)), "E", "F"),
                "The identity coordinate has zero acceleration, while the final coordinate has the second derivative of h."),
            AnalyticHelper("implicit_first_graph", "First differentiation of an implicit equation", Implicit(false, false),
                "The derivative of a constant zero germ vanishes. Applying the chain rule to the graph y mapped to (y,h(y)) gives the first implicit derivative equation."),
            AnalyticHelper("implicit_second_graph", "Second differentiation of an implicit equation", Implicit(false, true),
                "Differentiating the zero germ twice gives the outer second derivative on graph tangent vectors, plus the final-coordinate derivative applied to the acceleration of h."),
            AnalyticHelper("implicit_first_scalar", "Solving the first implicit derivative equation", Implicit(true, false),
                "For a scalar final coordinate, a nonzero final partial derivative permits division. The derivative of h is the negative ratio of the two partial derivatives."),
            AnalyticHelper("implicit_second_scalar", "Solving the second implicit derivative equation", Implicit(true, true),
                "The second derivative of h is the negative outer second derivative on graph tangent vectors divided by the final partial derivative."),
            AnalyticHelper("second_sub_const", "Constants do not affect second derivatives",
                ANormed(AAll(Eqn(D2(field, Lam("y", e, Sub(App("f", V("y")), V("c"))), x, v, w), D2(field, ff, x, v, w)),
                    ("f", Arr(e, fspace)), ("c", fspace), ("x", e), ("v", e), ("w", e)), "E", "F"),
                "Subtracting a constant leaves both derivatives unchanged."),
            AnalyticHelper("second_comp_clm", "Second derivatives under a linear change of variables",
                ANormed(AAll(Imp(Cd(field, ff, App("L", x)), Eqn(D2(field, Compose(ff, V("L")), x, v, w),
                    D2(field, ff, App("L", x), App("L", v), App("L", w)))),
                    ("L", Call("ContinuousLinearMap", field, e, fspace)), ("f", Arr(fspace, gspace)), ("x", e), ("v", e), ("w", e)), "E", "F", "G"),
                "A continuous linear inner map has zero second derivative. Its two images are the directions supplied to the outer second derivative."),
            AnalyticHelper("second_eq_derivative", "The bilinear second derivative",
                AAll(Imp(C2(ff, x), AAll(Eqn(D2(C, ff, x, v, w), Call("fderiv", C, Call("fderiv", C, ff), x, w, v)), allNvw)), nVectors),
                "For a complex C2 function, differentiating its derivative and then evaluating in v gives the same directional second derivative. This expression is complex bilinear in v and w."),
            AnalyticHelper("second_sub_sub", "Bilinearity on difference directions",
                AAll(Imp(C2(ff, x), AAll(Eqn(D2(C, ff, x, Sub(V("a"), V("b")), Sub(V("c"), V("d0"))),
                    Add(Sub(Sub(D2(C, ff, x, V("a"), V("c")), D2(C, ff, x, V("a"), V("d0"))),
                        D2(C, ff, x, V("b"), V("c"))), D2(C, ff, x, V("b"), V("d0")))),
                    ("a", shortN), ("b", shortN), ("c", shortN), ("d0", shortN))), nVectors),
                "Expanding both difference directions gives the four terms of a two-coordinate minor."),
            AnalyticHelper("second_complex_to_real", "Restriction from complex to real derivatives",
                AAll(Imp(C2(ff, x), AAll(Eqn(D2(R, ff, x, v, w), D2(C, ff, x, v, w)), allNvw)), nVectors),
                "The real derivative of a complex differentiable function is the scalar restriction of its complex derivative. Applying the same fact to the first derivative proves equality of the two second directional derivatives on complex vectors regarded as real vectors."),
            AnalyticHelper("second_angular_substitution", "The angular substitution negates the Hessian",
                AAll(Imp(C2(ff, D(0)), AAll(Eqn(D2(R,
                    Lam("theta", realN, App("f", Call("angularMap", V("theta")))), D(0), Single(j), Single(k)),
                    Neg(D2(C, ff, D(0), Single(j), Single(k)))), allNjk)),
                    ("n", N), ("f", Arr(shortN, C))),
                "The real angular map sends each coordinate vector to i times the corresponding complex vector. Complex bilinearity contributes i squared, hence a factor of minus one."),
            AnalyticHelper("logarithmicPhase_smooth", "Smoothness in logarithmic coordinates",
                AAll(AImps(C2(LogPhase(a, hh), D(0)), C2(hh, constantA), Member(h0)), nH),
                "The exponential coordinate map is entire. If h is complex C2 at the constant point and its value lies in the slit plane, composition with the principal logarithm is complex C2 at zero."),
            AnalyticHelper("fderiv_exponentialChart", "The first derivative of exponential coordinates",
                AAll(Eqn(D1(C, Chart(a), V("u"), v),
                    Lam("j", nIndex, Mul(Mul(a, Call("Complex.exp", App("u", j))), App("v", j)))),
                    ("n", N), ("a", C), ("u", shortN), ("v", shortN)),
                "The coordinate map u_j mapped to a exp(u_j) has derivative a exp(u_j) v_j in direction v."),
            AnalyticHelper("second_exponentialChart", "The second derivative of exponential coordinates",
                AAll(Eqn(D2(C, Chart(a), D(0), v, w), Lam("j", nIndex, Mul(Mul(a, App("v", j)), App("w", j)))),
                    ("n", N), ("a", C), ("v", shortN), ("w", shortN)),
                "At zero, the second derivative in directions v and w has coordinate a v_j w_j."),
            AnalyticHelper("second_clog", "The second derivative of a logarithm",
                AAll(AImps(AAll(Eqn(D2(C, Lam("y", shortN, Call("Complex.log", App("g", V("y")))), x, v, w),
                    Add(Mul(Mul(Neg(Call("Inv.inv", Sq(App("g", x)))), D1(C, gg, x, w)), D1(C, gg, x, v)),
                        Mul(Call("Inv.inv", App("g", x)), D2(C, gg, x, v, w)))), allNvw),
                    C2(gg, x), Member(App("g", x))), ("n", N), ("g", Arr(shortN, C)), ("x", shortN)),
                "The derivative of log(g) is g inverse times Dg. The product rule gives g inverse times the second derivative, minus the product of the two first derivatives divided by g squared."),
            AnalyticHelper("logarithmicPhase_second", "The logarithmic-coordinate Hessian",
                AAll(AImps(AAll(Eqn(D2(C, LogPhase(a, hh), D(0), Single(j), Single(k)),
                    Sub(Add(Mul(a, D2(C, hh, constantA, Single(j), Single(k))),
                        Call("ite", Eqn(j, k), dhj, D(0))), Mul(dhj, dhk))), allNjk),
                    Ne(a, D(0)), C2(hh, constantA), Eqn(h0, a), Member(a)), nH),
                "At h(a,...,a)=a, the exponential and logarithm chain rules give a times the second derivative of h, the diagonal first-derivative term, and minus the product of first derivatives."),
            AnalyticHelper("actual_hessian", "The angular Hessian in derivatives of the local solution",
                WithA(All("h", HType, AImps(AAll(Eqn(Call("hessian", hh, j, k),
                    Sub(Sub(Mul(D1(C, hh, ZVector, Single(j)), D1(C, hh, ZVector, Single(k))),
                        Mul(Call("z", V("d")), D2(C, hh, ZVector, Single(j), Single(k)))),
                        Call("ite", Eqn(j, k), D1(C, hh, ZVector, Single(j)), D(0)))),
                    ("j", ShortIndex), ("k", ShortIndex)), Le(D(3), V("d")), Call("IsLocalSolution", V("A"), hh)))),
                "The local solution takes the positive real value z at the base point, so the principal logarithm is smooth there. Combining logarithmic coordinates with the angular substitution gives H_jk=h_j h_k-z h_jk-delta_jk h_j, with all derivatives of h taken over the complex numbers at the base point."),
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

    private static Formula ANormed(Formula body, params string[] spaces)
    {
        var field = V("kappa");
        for (var i = spaces.Length - 1; i >= 0; --i)
        {
            var name = spaces[i];
            body = AAll(body, (name, V("Type")),
                (name + "Add", Call("NormedAddCommGroup", V(name))),
                (name + "Space", Call("NormedSpace", field, V(name))));
        }
        return AAll(body, ("kappa", V("Type")),
            ("fieldNorm", Call("NontriviallyNormedField", field)));
    }

    private static DocumentBlock AnalyticHelper(string name, string title, Formula statement, string prose) =>
        Describe.Lean(DescribeId.Create("wormald-analytic-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

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

    private static DocumentBlock HessianResolution() => new DocumentBlock.Section(
        H("The Hessian closed form and rational square"), Blocks(
            Helper("calH_closedForm", "The closed form for the analytic Hessian determinant",
                HessianClosedFormFormula(),
                "For every regular tournament of order d at least three and every complex C2 local solution h, the actual real angular Hessian determinant is d times det(d²I+S²) divided by det(d²I−S²). The Hessian is defined by two real Frechet derivatives of the logarithmic phase."),
            Describe.Lean(DescribeId.Create("wormald-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The rational-square conjecture"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Write C=½I+A and let J have every entry equal to one. Tournament completeness gives 2C=J+S. For nonzero coordinates y and nonsingular Q(y)=diag(2/y)−S, the matrix determinant lemma factors K(y) as det Q(y), the product of the coordinates y_j/2, and one minus the sum of all entries of Q(y) inverse. Call that inverse-entry sum alpha. At the constant point z=2/d, the resolvent is dI−S. Strict diagonal dominance makes it nonsingular, and regularity gives row and column sums 1/d for its inverse.")),
                    Paragraph(Text("The resolvent inverse and alpha are complex C2 near the constant point. Every first coordinate derivative of alpha there is 1/2. Its second derivative in coordinates j and k is z to the power minus two times V_jk+V_kj, minus z inverse when j=k, where V=(dI−S) inverse. The equation alpha(y,h(y))=1 holds on a neighbourhood for every local solution. Its first derivative gives each coordinate derivative of h equal to minus one; its second derivative gives the corresponding difference of four alpha second derivatives.")),
                    Paragraph(Text("The exponential coordinate chart and the principal logarithm are C2 at the base point because h takes the positive value z there. Applying the second Frechet chain rule and then substituting imaginary angular coordinates identifies the actual angular Hessian with minus R transpose T R. Here the columns of R are e_j−e_d and T=I−d(V+V transpose). Both row and column sums of T are minus one. The matrix whose columns are R followed by the all-ones vector has determinant d; conjugating T by this matrix gives diagonal blocks R transpose T R and minus d. Consequently det(R transpose T R)=−d det T.")),
                    Paragraph(Text("The resolvent identity gives T=−(d²I+S²)(d²I−S²) inverse. All required inverses follow from the nonzero shifted determinants. The order d is odd, so its determinant contributes one minus sign, while the angular Hessian has the even size d−1 and its overall minus sign does not change its determinant. This proves the displayed closed form for calH.")),
                    Paragraph(Text("Transposition identifies det(dI−S) with det(dI+S). Factoring the quadratic matrices therefore makes det(d²I−S²) the square of an integer. In odd dimension, det(S+idI) is a purely imaginary Gaussian integer; dividing it by i gives a nonzero integer, and det(d²I+S²) is its square. The quotient of these two quadratic determinants is thus the square of a nonzero rational. The closed form identifies this quotient with d divided by calH, and also gives nonvanishing of calH.")),
                    Paragraph(Text("Finally, every first coordinate derivative of K at the constant point equals −det(dI−S)/(2d^d), which is nonzero. The complex implicit function theorem supplies a C2 local solution with value z and the required equation germ. Together with the Hessian calculation for every such solution, this proves both clauses of the conjecture."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("wormald-2026-tournament-hessian-square"),
                    ResolutionKind.Proved))));

    private static Formula HessianQuadraticPlus => Call("Matrix.det",
        Add(Smul(new Formula.Power(Call("Nat.cast", V("d")), D(2)), D(1)), Mul(Skew, Skew)));
    private static Formula HessianQuadraticMinus => Call("Matrix.det",
        Sub(Smul(new Formula.Power(Call("Nat.cast", V("d")), D(2)), D(1)), Mul(Skew, Skew)));
    private static Formula HessianClosedFormFormula() => WithA(Imp(Le(D(3), V("d")),
        Imp(Call("IsRegularTournament", V("A")), All("h", HType,
            Imp(Call("IsLocalSolution", V("A"), V("h")),
                Eqn(Call("calH", V("h")),
                    Fr(Mul(Call("Nat.cast", V("d")), HessianQuadraticPlus), HessianQuadraticMinus)))))));

}
