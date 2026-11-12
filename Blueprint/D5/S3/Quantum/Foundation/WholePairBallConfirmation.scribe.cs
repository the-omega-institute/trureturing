using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class WholePairBallConfirmationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/WholePairBallConfirmation.";
    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] xs) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Ex(string s, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula In(Formula a, Formula b) => Seq(a, InMacro, Sp, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Leq, Sp, b);
    private static Formula Less(Formula a, Formula b) => Seq(a, F.Lt, Sp, b);
    private static Formula Ne(Formula a, Formula b) => Seq(a, Neq, Sp, b);
    private static Formula Norm(Formula x) => Seq(Vert, Sp, x, Vert);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula N => Seq(Mathbb, Grp(V("N")));
    private static Formula Space => V("V");
    private static Formula Cone => V("C");
    private static Formula Unit => V("u");
    private static Formula K => C("base", Cone, Unit);
    private static Formula P => C("pure", Cone, Unit);
    private static Formula Dual => C("LinearMap", R, Space, R);
    private static Formula App(Formula f, Formula x) => C("apply", f, x);
    private static Formula Pair(string name, Formula p, Formula q) => C(name, Cone, Unit, p, q);
    private static Formula Context(Formula body) => All("V", V("Type"), Seq(
        OpenBracket, C("NormedAddCommGroup", Space), CloseBracket, Sp,
        OpenBracket, C("NormedSpace", R, Space), CloseBracket, Sp,
        OpenBracket, C("FiniteDimensional", R, Space), CloseBracket, Sp,
        All("C", C("PointedCone", R, Space), All("u", Dual, body))));
    private static Formula Strict => All("x", Space, Imp(In(V("x"), Cone),
        Imp(Ne(V("x"), D(0)), Less(D(0), App(Unit, V("x"))))));
    private static Formula Chart(Formula p, Formula q) => Pair("BallChart", p, q);
    private static Formula Domain(Formula b) => C("EuclideanSpace", R, C("Fin", C("dim", b)));
    private static Formula Phi(Formula b, Formula n) => App(C("param", b), n);
    private static Formula Negate(Formula n) => Seq(F.Minus, n);
    private static Formula E(Formula p, Formula x) => App(C("supportEffect", V("h"), p), x);
    private static Formula Excluded(Formula p, Formula x) => Pair("excludes", p, x);
    private static Formula Mid(Formula x, Formula y) => Seq(Seq(Frac, Grp(D(1)), Grp(D(2))), Cdot, Open, x, Plus, y, Close);

    public DocumentDefinition Create()
    {
        Formula p = V("p"), q = V("q"), x = V("x"), y = V("y"), b = V("b"), n = V("n"), g = V("g");
        Formula zeros = All("p", P, All("x", Space, Imp(In(x, K), Iff(Excluded(p, x), Eq(E(p, x), D(0))))));
        Formula finite = All("p", P, All("n", N,
            All("x", Seq(C("Fin", n), To, Space), All("w", Seq(C("Fin", n), To, R),
                Imp(All("i", C("Fin", n), In(App(x, V("i")), K)),
                    Imp(All("i", C("Fin", n), Le(D(0), App(V("w"), V("i")))),
                        Imp(Eq(C("sum", V("w")), D(1)),
                            Iff(Excluded(p, C("weightedSum", V("w"), x)),
                                All("i", C("Fin", n), Imp(Lt(D(0), App(V("w"), V("i"))),
                                    Excluded(p, App(x, V("i"))))))))))));
        Formula consequences = And(C("reciprocalLeast", Cone, Unit),
            And(C("fullMixture", Cone, Unit), And(zeros,
                And(C("zeroMidpoint", Cone, Unit), And(C("allAntipodes", Cone, Unit), finite)))));
        Formula result = Context(Imp(C("IsClosed", Cone), Imp(Strict,
            Imp(Eq(C("span", R, Cone), Top), Imp(C("wholePairBalls", Cone, Unit),
                All("h", C("commonSupport", Cone, Unit), consequences))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Entire minimal-face balls and one common positive support per pure point construct reciprocal least confirming effects on the original cone.",
            H("Whole pair balls and global least confirmation"), Blocks(
                Paragraph(Text("Let V be a finite dimensional real normed space and C the original closed cone. Its real span is V, and the original real-linear unit u is strictly positive on every nonzero point of C. The entire base K, all global pure points P and the entire proper-effect interval are precisely CircuitBalancedConfirmation.base, pure and proper. Strict positivity excludes nonzero lines. The theorem also holds for the zero carrier, and hence includes every original nonzero carrier. Neither a proper upper bound for the supplied supports, least confirmation, reciprocity, effect extension, projectivity, spectrality nor a Jordan representation is assumed.")),
                Def("pairBase", "The entire smallest cone-face base", Context(All("p", Space, All("q", Space,
                    All("x", Space, Iff(In(x, Pair("pairBase", p, q)), And(In(x, K),
                        All("F", C("Face", Cone), Imp(In(p, V("F")), Imp(In(q, V("F")), In(x, V("F"))))))))))),
                    "Membership requires normalized positivity and membership in every original cone face containing p and q. This is the intersection defining the smallest cone face; no selected patch, section or exposed-face replacement is used."),
                Def("wholePairBalls", "All entire pair bases are finite balls", Context(
                    Iff(C("wholePairBalls", Cone, Unit), All("p", P, All("q", P, Imp(Ne(p, q), C("Nonempty", Chart(p, q))))))),
                    "A BallChart has a natural dimension d greater than zero, an affine map from EuclideanSpace R (Fin d) to the original V, injectivity on that entire Euclidean space, and equality of the image of the entire closed unit ball with pairBase(C,u,p,q). These are its only fields. Sphere purity, properness and leastness are conclusions. The dimension may vary with the pair; d=1, including classical segments, is retained."),
                Def("commonSupport", "One global positive support for all local antipodes", Context(
                    Iff(C("commonSupport", Cone, Unit), All("p", P, Ex("g", Dual,
                        And(All("x", Space, Imp(In(x, Cone), Le(D(0), App(g, x)))),
                            And(Lt(D(0), App(g, p)), All("q", P, Imp(Ne(p, q),
                                All("b", Chart(p, q), All("n", Domain(b), Imp(Eq(Norm(n), D(1)),
                                    Imp(Eq(Phi(b, n), p), Eq(App(g, Phi(b, Negate(n))), D(0)))))))))))))),
                    "The same real-linear g for p is nonnegative on the entire original cone, is strictly positive at p, and vanishes at p's antipode in every admissible chart for every distinct pure q. Quantification over all admissible charts avoids dependence on a chosen coordinate system. No upper bound by u is supplied. In a singleton base the pair quantifier is empty."),
                Def("supportEffect", "Normalize the single global support", Context(All("h", C("commonSupport", Cone, Unit),
                    All("p", P, Eq(C("supportEffect", V("h"), p),
                        Seq(C("inverse", App(C("choose", App(V("h"), p)), p)), Cdot, C("choose", App(V("h"), p))))))),
                    "Choose the support given by h at p once and divide that same functional by its strictly positive reading at p. All local restrictions belong to this one global functional. Its properness is proved subsequently."),
                Def("excludes", "The original binary zero relation", Context(All("p", Space, All("x", Space,
                    Iff(Excluded(p, x), Ex("f", Dual, And(Pair("confirms", p, V("f")), Eq(App(V("f"), x), D(0)))))))),
                    "There exists one original globally proper effect f confirming p and vanishing at x. This definition is used on normalized mixed x and on positive nonnormalized vectors; the latter extension does not impose normalization."),
                Def("zeroMidpoint", "Zero midpoint closure for all mixed states", Context(
                    Iff(C("zeroMidpoint", Cone, Unit), All("p", P, All("x", Space, All("y", Space,
                        Imp(In(x, K), Imp(In(y, K), Imp(Excluded(p, x), Imp(Excluded(p, y), Excluded(p, Mid(x, y))))))))))),
                    "The two initial mixed states may have different exclusion witnesses. The midpoint obtains a single confirming witness from the constructed least effect."),
                Def("allAntipodes", "Every pure point in every entire pair ball", Context(
                    Iff(C("allAntipodes", Cone, Unit), All("p", P, All("q", P, Imp(Ne(p, q),
                        All("b", Chart(p, q), All("n", Domain(b), Imp(Eq(Norm(n), D(1)),
                            Imp(In(Phi(b, n), P), Excluded(Phi(b, n), Phi(b, Negate(n)))))))))))),
                    "Every unit-sphere point in every entire pair ball, including pure points other than the original p and q, globally excludes its antipode. The proof also establishes that all sphere points are global pure points, so the explicit purity premise discards no sphere point."),
                Item("whole_pair_ball_confirmation", "Construct reciprocal least confirmation", result,
                    "Assume the original closed generating cone and strict unit, all entire pair balls B and the common-support condition H. Then reciprocalLeast and fullMixture hold on the original carrier. For every pure p and every mixed x in K, binary exclusion is equivalent to the constructed effect vanishing at x. The zero midpoint property and all-quantifier antipodal exclusion hold. For every natural n, arbitrary original mixed list x indexed by Fin n, and nonnegative weights summing to one, exclusion of their weighted sum is equivalent to exclusion of each positive-weight term. Repeated labels and zero weights are retained. weightedSum denotes the sum of w(i) times x(i).",
                    "For a nonnegative affine scalar function on a closed ball, write its linear part as inner(v,s). Evaluation at minus the normalized v yields a>=norm(v), including v=0. Zero at minus the unit n forces a=inner(v,n)=norm(v), so the Cauchy-Schwarz equality criterion gives v=a n. Normalizing the global support therefore yields (1+inner(n,s))/2 on every entire pair ball. These bounds at every global pure point extend to properness on the entire cone through the original cone_bound. Applying the same scalar argument to one minus any proper confirmer shows domination on each ball; nonneg_on_cone extends it to whole-cone leastness. Interchanging endpoints in the same chart gives reciprocity. The original circuit/mixture equivalence supplies fullMixture.",
                    "A cone face cuts out an extreme subset of the original base. Affine transport and the extreme-point theorem for Euclidean closed balls identify all sphere points as global pure points. For any such a and its antipode r, their midpoint is the ball center. Any cone face containing a and r contains this center; writing the center as the midpoint of any x in the ball and its opposite forces that face to contain every x. Thus the entire pair base of a,r equals the original entire ball. H applied to this pair gives the full antipodal conclusion. Leastness and the least effect itself give both directions of the mixed-state zero characterization. Nonnegative finite sums give the positive-weight characterization; the midpoint is its direct linear consequence."),
                Paragraph(Text("For the singleton base, the global support normalized at its only pure point still works: the construction never chooses a distinct pair in the equal-point branch. Zero effects, zero vectors and zero weights are retained in cone inequalities and finite sums. The theorem proves the forward construction of Quantum Origin V 88.10 and its stated zero consequences. It does not prove the converse from S to the ball conditions, the general finite EJA bridge, 88.3, 88.11 or any physical source, PRE, CP, H13/C13 or other chapter 87 consumer. No literature priority is asserted.")))));
    }

    private static DocumentBlock Def(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Owner + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static DocumentBlock Item(string name, string title, Formula formula, params string[] prose) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-')), DeclarationHandle.Create(Owner + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(), Blocks([.. prose.Select(p => Paragraph(Text(p)))]), DescribeRole.Theorem);
}
