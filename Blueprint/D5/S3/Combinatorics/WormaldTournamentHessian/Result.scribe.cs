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
                "The supplied source excerpt does not identify a printed page number. The formula includes existence of a complex C2 local solution and the same conclusion for every such solution. The rational is embedded into ℂ before squaring. This document states the conjecture; it does not assert a settling theorem."),
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
                "Transposition identifies the determinants of dI+S and dI−S. Factoring d²I−S² gives the square of the first determinant. Factoring d²I+S² and using odd dimension gives the square of det(S+idI)/i. Thus the quotient is the square of the previously constructed rational. This algebraic identity does not identify the quotient with d divided by the analytic Hessian determinant."),
            Helper("regularAlgebraicSquare", "The algebraic square for regular tournaments", WithA(Imp(Le(D(3), V("d")),
                Imp(Call("IsRegularTournament", V("A")), RationalSquare(QuadraticRatio())))),
                "Oddness of a regular tournament supplies the hypothesis of the quadratic determinant identity. The existence of a local solution and the identification with its angular Hessian remain separate assertions."),
            Helper("determinantAtBase", "The determinant vanishes at the expansion point", WithA(Imp(Le(D(3), V("d")),
                Imp(Call("IsRegularTournament", V("A")), Eqn(Call("K", V("A"), FullZVector), D(0))))),
                "The constant vector one is in the kernel of I−(½I+A)D_z: each row of ½I+A sums to d/2. Hence its determinant is zero."),
            Helper("polynomialSmooth", "Smoothness of the determinant polynomial", WithA(Call("ContDiff", C, D(2), Call("K", V("A")))),
                "The permutation expansion of the determinant expresses K as a finite sum of products of affine coordinate functions. It is complex C2 everywhere."),
            Helper("localSolutionOfInvertible", "A local solution from the implicit function theorem", WithA(Imp(Le(D(3), V("d")),
                Imp(Call("IsRegularTournament", V("A")), Imp(InvertibleLastDerivative,
                    Ex("h", HType, Call("IsLocalSolution", V("A"), V("h"))))))),
                "If the final-coordinate derivative at the expansion point is invertible, the complex implicit function theorem gives a C2 local solution. The zero value follows from the preceding determinant identity. This statement retains the invertibility hypothesis."))));

    private static DocumentBlock.Describe Definition(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("wormald-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
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
        Describe.Lean(DescribeId.Create("wormald-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
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
}
