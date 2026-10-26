using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.WormaldTournamentHessian;

internal sealed class DefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Regular tournament Hessians: defs.",
        H("Tournament Hessian: defs"), Blocks(
            Definition("IsRegularTournament", "Regular tournaments", RegularFormula(),
                "The adjacency is Boolean. Each diagonal entry is false, and for distinct vertices exactly one direction is true. The out-degree is the same natural number at every vertex. No oddness hypothesis is added.", literature: true),
            Definition("adjacency", "The integral adjacency matrix", WithA(All("i", Index, All("j", Index,
                Eqn(Call("adjacency", V("A"), V("i"), V("j")), Indicator(V("i"), V("j")))))),
                "True edges have integral entry one and false edges have integral entry zero.", literature: true),
            Definition("skewAdjacency", "The skew adjacency matrix", WithA(Eqn(Call("skewAdjacency", V("A")),
                Sub(Call("adjacency", V("A")), Call("Matrix.transpose", Call("adjacency", V("A")))))),
                "The integral matrix S is A minus its transpose. It has zero diagonal and entries in {−1,0,1}."),
            Definition("z", "The expansion point", All("d", N, Eqn(Call("z", V("d")), Fr(D(2), V("d")))),
                "The source defines z=2/d and the constant vector with this coordinate. Only d at least three enters the conjecture.", literature: true),
            Definition("K", "The determinant polynomial", WithA(All("y", FullVector,
                Eqn(Call("K", V("A"), V("y")), Call("Matrix.det", Sub(D(1),
                    Mul(Add(Smul(Fr(D(1), D(2)), D(1)), Call("Matrix.map", Call("adjacency", V("A")),
                        Call("Int.castRingHom", C))), Call("Matrix.diagonal", V("y")))))))),
                "The map Int.castRingHom embeds the integral adjacency into the complex numbers. Matrix multiplication retains the source's column scaling by y.", literature: true),
            Definition("appendLast", "The final implicit coordinate", AppendFormula(),
                "Fin.snoc appends the scalar after the first d−1 coordinates. The index is lifted by its natural value to Fin((d−1)+1); for d positive this is the order-preserving identification with Fin d. The case d=0 has no indices."),
            Definition("IsLocalSolution", "A complex C2 local solution", LocalFormula(),
                "The source uses an analytic function h. The encoding requires complex C2 regularity at the base point, which suffices for the Hessian: h(z′)=z, ContDiffAt over the complex scalar field of order two, and an equation holding eventually in the neighbourhood filter at z′. It imposes no global equation on h.", literature: true),
            Definition("phase", "Real angular coordinates", PhaseFormula(),
                "Complex.log is the principal logarithm. Its argument at zero is the positive real number z when h is a local solution and d is at least three.", literature: true),
            Definition("hessian", "The real angular Hessian", HessianFormula(),
                "The entry in row j and column k differentiates θ↦fderiv ℝ (phase h) θ (Pi.single j 1) once more over ℝ in the direction Pi.single k 1, at θ=0. Thus the definition uses fderiv of fderiv and keeps the complex-valued output.", literature: true),
            Definition("calH", "The Hessian determinant", WithH(Eqn(Call("calH", V("h")), Call("Matrix.det", Call("hessian", V("h"))))),
                "The determinant has d−1 rows and columns.", literature: true),
            Definition("claim", "Conjecture 6 with local existence", Eqn(V("claim"), ClaimFormula()),
                "The supplied source excerpt does not identify a printed page number. The formula includes existence of a complex C2 local solution and the same conclusion for every such solution. The rational is embedded into ℂ before squaring. The theorem result proves this full statement with the stated analytic definitions.", literature: true),
            Helper("regularDegree", "The degree and order identity", WithA(Imp(Le(D(3), V("d")),
                Imp(Call("IsRegularTournament", V("A")), Ex("r", N,
                    And(Eqn(V("d"), Add(Mul(D(2), V("r")), D(1))),
                        All("i", Index, Eqn(SumOver("j", Index, Call("adjacency", V("A"), V("i"), V("j"))), Call("Nat.cast", V("r"))))))))),
                "If the common out-degree is r, counting both orientations gives 2dr=d(d−1). Positivity of d gives d=2r+1, and every integral adjacency row sums to r."),
            Helper("regularOdd", "Regular tournaments have odd order", WithA(Imp(Le(D(3), V("d")),
                Imp(Call("IsRegularTournament", V("A")), Call("Odd", V("d"))))),
                "If every out-degree is r, summing the two orientations of each off-diagonal pair gives 2dr=d(d−1). Since d is positive, d=2r+1."),
            Helper("determinantAtBase", "The determinant vanishes at the expansion point", WithA(Imp(Le(D(3), V("d")),
                Imp(Call("IsRegularTournament", V("A")), Eqn(Call("K", V("A"), FullZVector), D(0))))),
                "The constant vector one is in the kernel of I−(½I+A)D_z: each row of ½I+A sums to d/2. Hence its determinant is zero."),
            new DocumentBlock.Section(H("Second variations"), Blocks(AnalyticNodes())),
            Definition("second", "Directional second derivatives",
                ANormed(AAll(Eqn(Call("second", V("kappa"), V("f"), V("x"), V("v"), V("w")),
                    Call("fderiv", V("kappa"), Lam("y", V("E"), Call("fderiv", V("kappa"), V("f"), V("y"), V("v"))), V("x"), V("w"))),
                    ("f", new Formula.TypeArrow(V("E"), V("F"))), ("x", V("E")), ("v", V("E")), ("w", V("E"))), "E", "F"),
                "The first direction is held fixed while the first derivative is differentiated in the second direction."))));

    private const string Prefix = "D5/S3/Combinatorics/WormaldTournamentHessian/Defs.";

    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/wormald2026tournaments");

    private static DocumentBlock.Describe Definition(string name, string title, Formula formula, string prose, bool literature = false) =>
        Describe.Lean(DescribeId.Create("wormald-" + name.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(),
            DefinitionContent(name, prose), DescribeRole.Definition);

    private static BlockSequence DefinitionContent(string name, string prose) => name switch
    {
        "K" => Blocks(DeterminantQuotation(), Paragraph(Text(prose))),
        "IsLocalSolution" => Blocks(LocalSolutionQuotation(), Paragraph(Text(prose))),
        "phase" => Blocks(PhaseQuotation(), Paragraph(Text(prose))),
        "calH" => Blocks(HessianQuotation(), Paragraph(Text(prose))),
        _ => Blocks(Paragraph(Text(prose)))
    };

    private static Formula SourceH => Seq(Mathcal, Sp, Grp(V("H")));

    private static Formula SourceY => Seq(Mathbf, Sp, Grp(V("y")));

    private static Formula SourceZ => Seq(Mathbf, Sp, Grp(V("z")));

    private static Formula Dots => Seq(Dot, Dot, Dot);

    private static Formula SourceF => Seq(Widetilde, Sp, Grp(V("f")));

    private static Formula Subscript(Formula value, Formula index) => new Formula.Subscript(value, index);

    private static Formula Yi(Formula i) => Subscript(V("y"), i);

    private static Formula SourceIndex => Sub(V("d"), D(1));

    private static Formula SourceD => Subscript(V("I"), V("d"));

    private static DocumentBlock DeterminantQuotation()
    {
        var entry = Subscript(V("B"), Seq(V("i"), V("j")));
        var diagonal = Eqn(Subscript(V("B"), Seq(V("i"), V("i"))),
            Sub(D(1), Mul(Fr(D(1), D(2)), Yi(V("i")))));
        var dy = Subscript(V("D"), V("y"));
        var coefficient = Parenthesized(Add(Mul(Fr(D(1), D(2)), SourceD), V("A")));
        var matrix = Eqn(V("B"), Sub(SourceD, Mul(coefficient, dy)));
        var diagonalMatrix = Eqn(dy, Call("diag", Yi(D(1)), Dots, Yi(V("d"))));
        var determinant = Seq(V("K"), F.Eq, new Formula.Apply(V("K"), [SourceY]), F.Eq, Call("det", V("B")));
        var baseVector = Eqn(SourceZ, Parenthesized(Seq(V("z"), Comma, V("z"), Comma, Dots, Comma, V("z"))));
        return Paragraph(
            Text("§1, equation (1.2) and its defining paragraph: “Define "), Math(V("B")),
            Text(" to be the matrix whose "), Math(Parenthesized(Seq(V("i"), Comma, V("j")))),
            Text(" entry "), Math(entry), Text(" is "), Math(Seq(Minus, Yi(V("j")))),
            Text(" if "), Math(Eqn(Subscript(V("A"), Seq(V("i"), V("j"))), D(1))),
            Text(" and 0 otherwise, except for diagonal entries "), Math(diagonal),
            Text(". That is, "), Math(matrix), Text(" where "), Math(diagonalMatrix),
            Text(". Let "), Math(determinant), Text(". Set "), Math(Eqn(V("z"), Fr(D(2), V("d")))),
            Text(" and "), Math(baseVector), Text(".”"));
    }

    private static DocumentBlock LocalSolutionQuotation() => Paragraph(
        Text("§1, defining paragraphs immediately preceding Theorem 4: “Writing "),
        Math(Subscript(V("K"), V("j"))), Text(" for the partial derivative of "), Math(V("K")),
        Text(" with respect to "), Math(Yi(V("j"))), Text(", it will be shown that "),
        Math(Ne(new Formula.Apply(Subscript(V("K"), V("d")), [SourceZ]), D(0))), Text(" and "),
        Math(Eqn(new Formula.Apply(V("K"), [SourceZ]), D(0))), Text(", so (e.g. by observing that "),
        Math(V("K")), Text(" is linear in "), Math(Yi(V("d"))), Text(") one may solve "),
        Math(Eqn(new Formula.Apply(V("K"), [SourceY]), D(0))), Text(" in the neighbourhood of "),
        Math(SourceZ), Text(" and obtain "), Math(Eqn(Yi(V("d")),
            new Formula.Apply(V("h"), [Yi(D(1)), Dots, Yi(SourceIndex)]))),
        Text(" for an analytic function "), Math(V("h")), Text(".”"));

    private static DocumentBlock PhaseQuotation() => Paragraph(
        Text("§1, defining paragraphs immediately preceding Theorem 4: “Define a function "),
        Math(SourceF), Text(" in the neighbourhood of "), Math(Parenthesized(Seq(D(0), Comma, D(0), Comma, Dots, Comma, D(0)))),
        Text(" (the "), Math(Parenthesized(SourceIndex)), Text("-dimensional vector) by "),
        Math(Eqn(new Formula.Apply(SourceF, [Subscript(Theta, D(1)), Dots, Subscript(Theta, SourceIndex)]),
            new Formula.Apply(Call("log"), [new Formula.Apply(V("h"), [
                Mul(V("z"), new Formula.Power(V("e"), Mul(V("i"), Subscript(Theta, D(1))))), Dots,
                Mul(V("z"), new Formula.Power(V("e"), Mul(V("i"), Subscript(Theta, SourceIndex))))])]))),
        Text(".”"));

    private static DocumentBlock HessianQuotation() => Paragraph(
        Text("§1, defining paragraphs immediately preceding Theorem 4: “Let "), Math(SourceH),
        Text(" denote the determinant of the Hessian (matrix of second order partials) of "), Math(SourceF),
        Text(" at "), Math(Eqn(Subscript(Theta, V("j")), D(0))), Text(" for "),
        Math(Seq(V("j"), F.Eq, D(1), Comma, Dots, Comma, SourceIndex)), Text(".”"));

    private static DocumentBlock Helper(string name, string title, Formula statement, string prose) =>
        Describe.Lean(DescribeId.Create("wormald-" + name.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

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

        Formula Germ(Formula f, Formula value, Formula domain, Formula x) =>
            Call("Filter.EventuallyEq", Call("nhds", x), f, Lam("y", domain, value));
        Formula Member(Formula value) => Call("Membership.mem", Call("Complex.slitPlane"), value);
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
                "The local solution takes the positive real value z at the base point, so the principal logarithm is smooth there. Combining logarithmic coordinates with the angular substitution gives H_jk=h_j h_k-z h_jk-delta_jk h_j, with all derivatives of h taken over the complex numbers at the base point.")
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

    private static Formula ANormed(Formula body, params string[] spaces)
    {
        var field = V("kappa");
        for (var i = spaces.Length - 1; i >= 0; --i)
        {
            var name = spaces[i];
            body = All(name, V("Type"), Instances(body,
                Call("NormedAddCommGroup", V(name)), Call("NormedSpace", field, V(name))));
        }
        return All("kappa", V("Type"), Instances(body, Call("NontriviallyNormedField", field)));
    }

    private static DocumentBlock AnalyticHelper(string name, string title, Formula statement, string prose) =>
        Describe.Lean(DescribeId.Create("wormald-analytic-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

}
