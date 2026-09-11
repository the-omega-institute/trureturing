using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class TwoPointSlabSupportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithSums/TwoPointSlabSupport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An actual two-corner budget slab has positive support, strictly above the base at zero shape.",
        H("Support of a two-point coordinate box"),
        Blocks(
            Paragraph(Text("All logarithms are natural. The support theorem uses three coordinates "
                + "with widths log(2), log(3), log(7). All budgets, heights and shape coordinates "
                + "are arbitrary finite real numbers. The notation xi denotes the source shape; "
                + "its minimum is zero exactly when some coordinate is zero, since every coordinate "
                + "is nonnegative. The variance sum below is unaveraged.")),
            Entry("pairDistance", "pair-distance", "Distance to an actual pair",
                Lines(Seq(All(S, Call("Set", Alpha)), All(C, Alpha), All(Dd, Alpha),
                    Equal(Pair(S, C, Dd), Call("min", Call("infDist", C, S),
                        Call("infDist", Dd, S))))),
                "Here alpha is any pseudometric space and S is any subset. Each infDist is the "
                + "usual point-to-set infimum distance. For a nonempty compact S the minimum "
                + "has the attained-distance meaning proved below.", DescribeRole.Definition),
            Entry("IsCorner", "actual-corner", "One actual endpoint in every coordinate",
                Lines(Seq(All(C, Arrow(Iota, Alpha)), All(Dd, Arrow(Iota, Alpha)),
                    All(X, Arrow(Iota, Alpha)), Equivalent(Corner(X),
                        Seq(All(I, Iota), Member(Sub(X, I), PairSet(Sub(C, I), Sub(Dd, I))))))),
                "The index type and coordinate type are arbitrary. Endpoint coincidence is "
                + "allowed in this definition. Fractional coordinate mixtures are not corners.",
                DescribeRole.Definition),
            Entry("WideSlab", "wide-slab", "Two different included budget values",
                Lines(Seq(All(C, Arrow(Iota, Reals)), All(Dd, Arrow(Iota, Reals)),
                    All(M0, Reals), All(M1, Reals), Equivalent(Wide,
                        Ands(Less(M0, M1), Seq(Some(X, Arrow(Iota, Reals)),
                            Some(Y, Arrow(Iota, Reals)), Ands(Corner(X), Corner(Y),
                                Member(Budget(X), Interval(M0, M1)),
                                Member(Budget(Y), Interval(M0, M1)),
                                Unequal(Budget(X), Budget(Y)))))))),
                "The index type iota is finite. A budget is the sum of all coordinates. "
                + "Both slab endpoints are included. Two corner labels with the same budget "
                + "do not meet this hypothesis: the actual budget values must differ.",
                DescribeRole.Definition),
            Entry("logWidths", "logarithmic-widths", "The exact ordered widths",
                Lines(Equal(Hvec, Paren(Seq(LogOf(2), Comma, LogOf(3), Comma, LogOf(7))))),
                "The vector h is indexed by Fin(3), in this displayed order. In particular, "
                + "a=log(2)>0, and a is no larger than either other width.", DescribeRole.Definition),
            Entry("pair_distance_spec", "attained-distance", "The minimum is the genuine set distance",
                Lines(Seq(All(S, Call("Set", Alpha)), All(C, Alpha), All(Dd, Alpha),
                    ImpliesTo(Ands(Call("IsCompact", S), Unequal(S, Emptyset)),
                        DistanceSpec(S, C, Dd, Pair(S, C, Dd))))),
                "In any pseudometric space, compactness and nonemptiness give a closest point "
                + "of S to each endpoint. Choose the endpoint with the smaller infimum. The "
                + "result is attained by an actual pair and bounds the distance of every actual "
                + "pair from below. These properties identify the set-to-set minimum; a merely "
                + "supplied nonnegative lower bound would not have this meaning."),
            Entry("wide_slab_support_237", "complete-support", "The complete three-coordinate support theorem",
                SupportStatement(),
                "In the displayed statement, all unqualified coordinate sums and coordinate "
                + "quantifiers range over Fin(3). Bool choices are identified with bits zero and "
                + "one. Thus e_i h_i means h_i for true and zero for false. The symbol o is the "
                + "offset function, and its range consists of the actual corner offsets. IsLeast "
                + "asserts membership as well as a lower bound: zero and a are both attained. "
                + "The bracketed conclusions are a conjunction under the displayed hypotheses. "
                + "Every included corner is quantified, not only the two witnessing the slab.",
                DescribeRole.Theorem),
            Paragraph(Text("For an included corner, its mean lies in the scaled closed budget "
                + "interval. The attained-distance comparison gives delta_i <= |x_i-m|. Squaring "
                + "and summing proves the first variance inequality. With w_i=x_i-T>=0, the "
                + "identity sum(w_i)=3(m-T) and the nonnegative cross terms in its square give "
                + "sum(w_i^2)<=(sum(w_i))^2. Subtracting 3(m-T)^2 gives the factor six. "
                + "The generic finite-index square-sum argument specializes to three coordinates.")),
            Paragraph(Text("Every nonzero bit offset includes at least one positive width, and "
                + "each width is at least a. The all-false choice attains zero; choosing only "
                + "the first coordinate attains a. In zero shape, two different included budget "
                + "values therefore force v>=a. The strict slab order gives u<v.")),
            Paragraph(Text("If u<=0, the base T lies in the mean interval and every coordinate "
                + "distance vanishes. If u>0, the left interval endpoint bounds every distance "
                + "by u/3. Summing the three squared bounds yields rho<=u/(3 sqrt(2)). Since "
                + "sqrt(2)>1 and v>u>0, the displayed intermediate lower bound is strictly "
                + "greater than T. In either branch the offsets lambda=L-T and eta=H-T "
                + "satisfy 0<lambda<=eta; lambda is an offset, not a dual price.")),
            Paragraph(Text("Negative lower budgets, arbitrary upper slack, corners at either "
                + "closed endpoint, zero w coordinates and zero variance are included. No "
                + "integer exponent, coordinate-width comparison c_i>=h_i, cutoff, small-shape "
                + "or physical premise is imposed. The result supplies positive arguments for "
                + "later arithmetic analytic estimates; it makes no quantum or RH assertion.")))));

    private static Formula SupportStatement()
    {
        Formula cornerRepresentation = Seq(All(X, Vectors), Equivalent(Corner(X),
            Seq(Some(E, Bits), Equal(X, Paren(Seq(I, Sp, Mapsto, Sp,
                PlusOf(Sub(C, I), BitTerm)))))));
        Formula budgetRepresentation = Seq(All(E, Bits),
            Equal(SumOf(PlusOf(Sub(C, I), BitTerm)), PlusOf(A, Offset(E))));
        Formula cornerBounds = Seq(All(X, Vectors), ImpliesTo(
            Ands(Corner(X), Member(Budget(X), Interval(M0, M1))),
            Seq(Let(Equal(M, Div(Budget(X), D(3)))),
                Ands(Member(M, IntervalI), Seq(All(I, Fin3), Nonnegative(SubtractOf(Sub(X, I), T))),
                    Seq(V0, Sp, Le, Sp, SumOf(Square(Paren(SubtractOf(Sub(X, I), M)))),
                        Sp, Eq, Sp, CenteredExpansion, Sp, Le, Sp,
                        TimesOf(D(6), Square(Paren(SubtractOf(M, T))))),
                    Seq(D(0), Sp, Le, Sp, Rho, Sp, Le, Sp, SubtractOf(M, T),
                        Sp, Le, Sp, SubtractOf(Mu, T))))));
        Formula zeroBranch = ImpliesTo(Seq(U, Sp, Le, Sp, D(0)), Ands(
            Seq(All(I, Fin3), Equal(Sub(DeltaLower, I), D(0))), Equal(Rho, D(0)),
            Equal(L, PlusOf(T, Div(V, D(3)))), Less(T, L)));
        Formula positiveBranch = ImpliesTo(Positive(U), Ands(
            Seq(All(I, Fin3), Sub(DeltaLower, I), Sp, Le, Sp, Div(U, D(3))),
            Seq(Rho, Sp, Le, Sp, Div(U, TimesOf(D(3), Root(D(2))))),
            Seq(L, Sp, Ge, Sp, StrictLower, Sp, Gt, Sp, T)));
        Formula zeroShape = ImpliesTo(Equal(XiShape, D(0)), Seq(
            Let(Equal(U, SubtractOf(M0, TimesOf(D(3), T)))),
            Let(Equal(V, SubtractOf(M1, TimesOf(D(3), T)))),
            Ands(Seq(Alog, Sp, Le, Sp, V), Less(U, V), zeroBranch, positiveBranch,
                Seq(D(0), Sp, Lt, Sp, SubtractOf(L, T), Sp, Le, Sp, SubtractOf(H, T)))));
        return Lines(
            Seq(All(T, Reals), All(M0, Reals), All(M1, Reals), All(XiShape, Vectors)),
            Let(Seq(Equal(Alog, LogOf(2)), Comma, Sp,
                Equal(Hvec, Paren(Seq(LogOf(2), Comma, LogOf(3), Comma, LogOf(7)))))),
            Let(Seq(Equal(Sub(C, I), PlusOf(T, Sub(XiShape, I))), Comma, Sp,
                Equal(Sub(Dd, I), PlusOf(Sub(C, I), Sub(Hvec, I))), Comma, Sp,
                Equal(A, PlusOf(TimesOf(D(3), T), SumOf(Sub(XiShape, I)))))),
            Let(Seq(Equal(IntervalI, Interval(Div(M0, D(3)), Div(M1, D(3)))), Comma, Sp,
                Equal(Mu, Div(M1, D(3))), Comma, Sp,
                Equal(Sub(DeltaLower, I), Pair(IntervalI, Sub(C, I), Sub(Dd, I))))),
            Let(Seq(Equal(V0, SumOf(Square(Sub(DeltaLower, I)))), Comma, Sp,
                Equal(Rho, Root(Div(V0, D(6)))), Comma, Sp,
                Equal(L, SubtractOf(Mu, Rho)), Comma, Sp,
                Equal(H, PlusOf(Mu, TimesOf(D(2), Rho))))),
            Let(Equal(O, Paren(Seq(Paren(Seq(E, Colon, Bits)), Sp, Mapsto, Sp, SumOf(BitTerm))))),
            Seq(Ands(Seq(Alog, Sp, Le, Sp, T), Seq(All(I, Fin3), Nonnegative(Sub(XiShape, I))),
                Seq(Some(I, Fin3), Equal(Sub(XiShape, I), D(0))), Wide), Sp, Implies),
            Seq(Grp(), OpenBracket, Paren(cornerRepresentation)),
            Seq(Land, Sp, Paren(budgetRepresentation)),
            Seq(Land, Sp, Paren(Seq(All(I, Fin3),
                DistanceSpec(IntervalI, Sub(C, I), Sub(Dd, I), Sub(DeltaLower, I))))),
            Seq(Land, Sp, Paren(cornerBounds)),
            Seq(Land, Sp, H, Sp, Ge, Sp, L, Sp, Ge, Sp, T, Sp, Gt, Sp, D(0)),
            Seq(Land, Sp, Call("IsLeast", Call("range", O), D(0)), Sp, Land, Sp,
                Call("IsLeast", Seq(OpenBrace, R, Sp, Mid, Sp,
                    Ands(Member(R, Call("range", O)), Positive(R)), CloseBrace), Alog)),
            Seq(Land, Sp, Paren(zeroShape), CloseBracket));
    }

    private static DocumentBlock Entry(string name, string id, string title, Formula formula,
        string explanation, DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), role);

    private static Formula DistanceSpec(Formula set, Formula c, Formula d, Formula delta) => Ands(
        Nonnegative(delta), Seq(Some(Y, set), Some(Z, PairSet(c, d)),
            Equal(delta, Call("dist", Y, Z))),
        Seq(All(Y, set), All(Z, PairSet(c, d)), delta, Sp, Le, Sp, Call("dist", Y, Z)));
    private static Formula Lines(params Formula[] rows) => Disp(new Formula.Aligned([.. rows]));
    private static Formula Pair(Formula set, Formula c, Formula d) => Call("pairDistance", set, c, d);
    private static Formula Corner(Formula x) => Call("IsCorner", C, Dd, x);
    private static Formula Wide => Call("WideSlab", C, Dd, M0, M1);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula All(Formula name, Formula domain) => Seq(Forall, Sp, name,
        Sp, InMacro, Sp, domain, Comma, Sp);
    private static Formula Some(Formula name, Formula domain) => Seq(Exists, Sp, name,
        Sp, InMacro, Sp, domain, Comma, Sp);
    private static Formula Let(Formula body) => Seq(Operatorname, Grp(F.Id("let")), Sp, body, Semi, Sp);
    private static Formula Arrow(Formula source, Formula target) => Paren(Seq(source, Sp, To, Sp, target));
    private static Formula Budget(Formula x) => SumOf(Sub(x, I));
    private static Formula SumOf(Formula body) => Seq(Sum, Underscore, Grp(I), Sp, Paren(body));
    private static Formula Sub(Formula value, Formula index) => Seq(value, Underscore, Grp(index));
    private static Formula Square(Formula value) => Seq(value, Caret, Grp(D(2)));
    private static Formula Root(Formula value) => Seq(Sqrt, Grp(value));
    private static Formula Div(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula LogOf(byte value) => Seq(Log, Sp, D(value));
    private static Formula Paren(Formula value) => Seq(Open, value, Close);
    private static Formula PairSet(Formula a, Formula b) => Seq(OpenBrace, a, Comma, Sp, b, CloseBrace);
    private static Formula Interval(Formula a, Formula b) => Seq(OpenBracket, a, Comma, Sp, b, CloseBracket);
    private static Formula PlusOf(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula SubtractOf(Formula a, Formula b) => Seq(a, Sp, Minus, Sp, b);
    private static Formula TimesOf(Formula a, Formula b) => Seq(a, Sp, Cdot, Sp, b);
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Unequal(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula Less(Formula a, Formula b) => Seq(a, Sp, Lt, Sp, b);
    private static Formula Member(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula Positive(Formula value) => Less(D(0), value);
    private static Formula Nonnegative(Formula value) => Seq(D(0), Sp, Le, Sp, value);
    private static Formula Equivalent(Formula a, Formula b) => Seq(Paren(a), Sp, Iff, Sp, Paren(b));
    private static Formula ImpliesTo(Formula a, Formula b) => Seq(Paren(a), Sp, Implies, Sp, Paren(b));
    private static Formula Ands(params Formula[] parts) => Seq(parts.SelectMany((part, index) =>
        index == 0 ? new[] { Paren(part) } : new[] { Sp, Land, Sp, Paren(part) }).ToArray());

    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Fin3 => Call("Fin", D(3));
    private static Formula Vectors => Arrow(Fin3, Reals);
    private static Formula Bits => Arrow(Fin3, PairSet(D(0), D(1)));
    private static Formula XiShape => Seq(Operatorname, Grp(F.Id("xi")));
    private static Formula I => F.Id("i");
    private static Formula S => F.Id("S");
    private static Formula C => F.Id("c");
    private static Formula Dd => F.Id("d");
    private static Formula X => F.Id("x");
    private static Formula Y => F.Id("y");
    private static Formula Z => F.Id("z");
    private static Formula E => F.Id("e");
    private static Formula O => F.Id("o");
    private static Formula R => F.Id("r");
    private static Formula T => F.Id("T");
    private static Formula A => F.Id("A");
    private static Formula Alog => F.Id("a");
    private static Formula Hvec => F.Id("h");
    private static Formula M => F.Id("m");
    private static Formula M0 => Sub(F.Id("M"), D(0));
    private static Formula M1 => Sub(F.Id("M"), D(1));
    private static Formula IntervalI => F.Id("I");
    private static Formula V0 => Sub(F.Id("V"), D(0));
    private static Formula L => F.Id("L");
    private static Formula H => F.Id("H");
    private static Formula U => F.Id("u");
    private static Formula V => F.Id("v");
    private static Formula Offset(Formula e) => new Formula.Apply(O, [e]);
    private static Formula BitTerm => TimesOf(Sub(E, I), Sub(Hvec, I));
    private static Formula CenteredExpansion => SubtractOf(
        SumOf(Square(Paren(SubtractOf(Sub(X, I), T)))),
        TimesOf(D(3), Square(Paren(SubtractOf(M, T)))));
    private static Formula StrictLower => PlusOf(T, Div(SubtractOf(V, Div(U, Root(D(2)))), D(3)));
}
