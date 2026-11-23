using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.OrderScores;

internal sealed class QubitJensenShannonDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/Divergence/wu2026measurementorder");
    private static readonly Formula R = Seq(Mathbb, Grp(F.Id("R")));
    private static readonly Formula N = Seq(Mathbb, Grp(F.Id("N")));
    private static readonly Formula Bool = F.Id("Bool");
    private static readonly Formula Outcomes = Seq(Bool, Sp, Times, Sp, Bool);
    private static readonly Formula State = Call("DensityState", Call("Fin", D(2)));
    private static readonly Formula Matrix = Call("Matrix", Call("Fin", D(2)), Call("Fin", D(2)),
        Seq(Mathbb, Grp(F.Id("C"))));
    private static readonly Formula Pair = Seq(R, Sp, Times, Sp, R);
    private static readonly Formula Measurement = new Formula.TypeArrow(Bool, Matrix);
    private static readonly Formula Zero = D(0);
    private static readonly Formula One = D(1);
    private static readonly Formula Two = D(2);
    private static readonly Formula Half = Fr(One, Two);
    private static readonly Formula LogTwo = Call("ln", Two);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Jensen–Shannon order score for two sharp qubit measurements.",
        H("Qubit Jensen–Shannon order score"),
        Blocks(
            Paragraph(DefinitionDsl.Text("Every square root uses Lean’s total real convention. It is the nonnegative square root of the maximum of zero and its argument, so a negative argument gives zero.")),
            Definition("outcomeSign", "Outcome signs", "The two Boolean outcomes represent the signs −1 and +1.",
                All("a", Bool, Equal(Call("outcomeSign", X("a")), Call("ite", X("a"), One, Negate(One))))),
            Definition("projector", "Pauli effects", "In the bisector frame the Bloch axis has coordinates (k, 0, m).",
                All("m", R, All("k", R, All("a", Bool, Equal(P("m", "k", X("a")),
                    Call("qubitMatrix", Mul(Call("outcomeSign", X("a")), X("k")),
                        Mul(Call("outcomeSign", X("a")), X("m")))))))),
            Definition("nativeMatrix", "Native state matrix",
                "A DensityState on Fin 2 is a positive semidefinite complex operator of trace one. The matrix conversion preserves the operator and its trace.",
                All("r", State, Equal(Call("nativeMatrix", X("r")),
                    Call("ofMatrixSymm", Seq(X("r"), Dot, F.Id("val")))))),
            Definition("sOfT", "Parity parameter", "The acute branch selects the smaller parity mass.",
                All("t", R, Equal(Call("sOfT", X("t")),
                    Fr(Sub(One, Root(Sub(One, Mul(D(4), Sq(X("t")))))), Two)))),
            Theorem("parameter_calibration", "Parity calibration", "The smaller parity mass lies in the closed half interval and determines the square of the order parameter.",
                All("t", R, Imp(InHalf(X("t")),
                    Both(InHalf(Call("sOfT", X("t"))),
                        Equal(Mul(Call("sOfT", X("t")), Sub(One, Call("sOfT", X("t")))), Sq(X("t"))))))),
            Definition("jointRecord", "Forward Lüders record",
                "The first coordinate belongs to the measurement performed first.",
                All("A", Measurement, All("B", Measurement, All("r", State, All("o", Outcomes,
                    Equal(Call("jointRecord", X("A"), X("B"), X("r"), X("o")),
                        TraceEffect(Call("A", Fst(X("o"))), Call("B", Snd(X("o"))))))))),
                AssessedProvenance.FromLiterature(Wu)),
            Definition("orderScore", "Lüders order score",
                "Definition 1 uses Shannon entropy in bits. The two records use the same density state and label entries by the outcome of each measurement. H denotes finite Shannon entropy in nats and division by ln 2 converts the divergence to bits.",
                OrderScore(), AssessedProvenance.FromLiterature(Wu)),
            Definition("sourceScore", "Bisector-frame score", "In X, Y, Z order the two sharp Bloch axes are (k, 0, m) and (−k, 0, m).",
                All("t", R, All("r", State, Let("s", Call("sOfT", X("t")),
                    Let("m", Root(Sub(One, X("s"))), Let("k", Root(X("s")),
                        Equal(Call("sourceScore", X("t"), X("r")),
                            Call("orderScore", P("m", "k"), Call("projector", X("m"), Negate(X("k"))), X("r"))))))))),
            Definition("psi", "Optimized score",
                "Section II.C maximizes over all common native qubit inputs. The equality of the supremum with an attained maximum is proved below.",
                All("t", R, Equal(Call("psi", X("t")), Call("sSup", Call("range", Call("sourceScore", X("t")))))),
                AssessedProvenance.FromLiterature(Wu)),
            Definition("disk", "Closed Bloch disk",
                "Only the two coordinates in the plane of the measurement axes affect the two records.",
                Equal(X("disk"), Seq(OpenBrace, X("d"), Colon, Sp, Pair, Sp, Mid, Sp,
                    Le(SqNorm(X("d")), One), CloseBrace))),
            Definition("diskScore", "Score in Bloch coordinates",
                "The deficit g(y) is ln 2 minus the binary entropy in nats at (1+y)/2. The parity masses are 1−s and s. Grouping by parity cancels the common parity entropy, including when a parity has zero mass.",
                All("s", R, All("d", Pair, Let("u", BiasU("s", "d"), Let("v", BiasV("s", "d"),
                    Equal(Call("diskScore", X("s"), X("d")), Fr(DeficitCombination(), LogTwo))))))),
            Theorem("native_maximum", "Attainment on the disk and in the native states",
                "Every disk point has a native realization, and a compactness argument attains the common largest score. The existential state and disk point use the same value of the optimization parameter.",
                NativeMaximum()),
            Definition("circlePoint", "First-quadrant circle",
                "The squared X coordinate is the parameter w. On the unit interval the squared Z coordinate is 1−w.",
                All("w", R, Equal(Call("circlePoint", X("w")), Tuple(Root(X("w")), Root(Sub(One, X("w"))))))),
            Definition("seriesWeight", "Entropy series weight",
                "The even entropy series starts with degree two. The index is a natural number and its appearances in the weight are real casts.",
                All("n", N, Equal(Call("seriesWeight", X("n")),
                    Fr(One, Mul(Add(Mul(Two, Call("realCast", X("n"))), Two),
                        Add(Mul(Two, Call("realCast", X("n"))), One)))))),
            Theorem("series_weight_pos", "Positive weights", "All degrees have positive weights.",
                All("n", N, Less(Zero, Call("seriesWeight", X("n"))))),
            Definition("coeff", "Even coefficient", "The two original biases are u+v and u−v, and u and v are the parity biases of the mixture.",
                All("n", N, All("s", R, All("u", R, All("v", R,
                    Equal(Call("coeff", X("n"), X("s"), X("u"), X("v")), Coefficient())))))),
            Theorem("coeff_zero", "Quadratic coefficient", "The mixed terms cancel at degree two.",
                All("s", R, All("u", R, All("v", R,
                    Equal(Call("coeff", Zero, X("s"), X("u"), X("v")),
                        Add(Mul(X("s"), Sq(X("u"))), Mul(Sub(One, X("s")), Sq(X("v"))))))))),
            Definition("diskCoeff", "Disk coefficients", "The disk coordinates determine all four biases.",
                All("n", N, All("s", R, All("d", Pair, Equal(DiskCoeff("n", "s", "d"),
                    Call("coeff", X("n"), X("s"), BiasU("s", "d"), BiasV("s", "d"))))))),
            Theorem("disk_series", "Closed-disk entropy series",
                "Uniform convergence of the scalar entropy series on the closed bias interval allows biases of magnitude one.",
                All("s", R, All("d", Pair, Imp(Both(Member(X("s"), Closed(Zero, One)), Member(X("d"), X("disk"))),
                    Call("HasSum", Lam("n", N, Mul(Call("seriesWeight", X("n")), DiskCoeff("n", "s", "d"))),
                        Mul(Call("diskScore", X("s"), X("d")), LogTwo)))))),
            Theorem("disk_score_le_of_coeff_le", "Coefficientwise comparison",
                "A comparison between two disk points at possibly different parity weights lifts to the entropy score.",
                CoefficientComparison())), []));

    private static DocumentBlock Definition(string name, string title, string prose, Formula statement,
        AssessedProvenance? provenance = null) =>
        DescribeNode(name, title, prose, statement, DescribeRole.Definition, provenance);

    private static DocumentBlock Theorem(string name, string title, string prose, Formula statement,
        AssessedProvenance? provenance = null) =>
        DescribeNode(name, title, prose, statement, DescribeRole.Theorem, provenance);

    private static DocumentBlock DescribeNode(string name, string title, string prose, Formula statement,
        DescribeRole role, AssessedProvenance? provenance) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(statement)),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(DefinitionDsl.Text(prose))), role);

    private static Formula OrderScore()
    {
        var ab = TraceEffect(Call("A", X("a")), Call("B", X("b")));
        var ba = TraceEffect(Call("B", X("b")), Call("A", X("a")));
        var mix = Lam("o", Outcomes,
            Fr(Add(Call("p", X("o")), Call("q", X("o"))), Two));
        return All("A", Measurement, All("B", Measurement, All("r", State,
            Let("p", Lam("o", Outcomes, Let("a", Fst(X("o")), Let("b", Snd(X("o")), ab))),
                Let("q", Lam("o", Outcomes, Let("a", Fst(X("o")), Let("b", Snd(X("o")), ba))),
                    Equal(Call("orderScore", X("A"), X("B"), X("r")), Fr(
                        Sub(Call("H", mix), Fr(Add(Call("H", X("p")), Call("H", X("q"))), Two)), LogTwo)))))));
    }

    private static Formula TraceEffect(Formula first, Formula second) =>
        Call("Re", Call("Tr", Mul(Call("nativeMatrix", X("r")), Mul(Mul(first, second), first))));

    private static Formula NativeMaximum()
    {
        var score = Call("psi", X("t"));
        var parity = Call("sOfT", X("t"));
        var diskUpper = All("x", Pair, Imp(Member(X("x"), X("disk")),
            Le(Call("diskScore", parity, X("x")), score)));
        var stateUpper = All("q", State, Le(Call("sourceScore", X("t"), X("q")), score));
        var maximum = Both(Equal(Call("sourceScore", X("t"), X("r")), score),
            Both(Equal(Call("diskScore", parity, X("d")), score), Both(diskUpper, stateUpper)));
        return All("t", R, Imp(InHalf(X("t")), Bind(FormulaQuantifier.Exists, "d", Pair,
            Both(Member(X("d"), X("disk")), Bind(FormulaQuantifier.Exists, "r", State, maximum)))));
    }

    private static Formula CoefficientComparison() =>
        All("s", R, All("t", R, All("d", Pair, All("e", Pair,
            Imp(Both(Member(X("s"), Closed(Zero, One)), Both(Member(X("t"), Closed(Zero, One)),
                Both(Member(X("d"), X("disk")), Member(X("e"), X("disk"))))),
                Imp(All("n", N, Le(DiskCoeff("n", "s", "d"), DiskCoeff("n", "t", "e"))),
                    Le(Call("diskScore", X("s"), X("d")), Call("diskScore", X("t"), X("e")))))))));

    private static Formula Coefficient()
    {
        var degree = Add(Mul(Two, X("n")), Two);
        return Sub(Sub(Fr(Add(Pow(Add(X("u"), X("v")), degree), Pow(Sub(X("u"), X("v")), degree)), Two),
            Mul(Sub(One, X("s")), Pow(X("u"), degree))), Mul(X("s"), Pow(X("v"), degree)));
    }

    private static Formula DeficitCombination() =>
        Sub(Sub(Fr(Add(Call("g", Add(X("u"), X("v"))), Call("g", Sub(X("u"), X("v")))), Two),
            Mul(Sub(One, X("s")), Call("g", X("u")))), Mul(X("s"), Call("g", X("v"))));

    private static Formula DiskCoeff(string n, string s, string d) => Call("diskCoeff", X(n), X(s), X(d));
    private static Formula BiasU(string s, string d) => Mul(Root(Sub(One, X(s))), Snd(X(d)));
    private static Formula BiasV(string s, string d) => Mul(Root(X(s)), Fst(X(d)));
    private static Formula SqNorm(Formula d) => Add(Sq(Fst(d)), Sq(Snd(d)));
    private static Formula P(string m, string k, params Formula[] outcomes) => Call("projector", [X(m), X(k), .. outcomes]);
    private static Formula X(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(X(name))), [.. args]);
    private static Formula Group(Formula a) => Seq(Open, a, Close);
    private static Formula Tuple(Formula a, Formula b) => Seq(Open, a, Comma, Sp, b, Close);
    private static Formula Closed(Formula a, Formula b) => Seq(OpenBracket, a, Comma, Sp, b, CloseBracket);
    private static Formula InHalf(Formula a) => Member(a, Closed(Zero, Half));
    private static Formula Fst(Formula a) => Seq(a, Dot, D(1));
    private static Formula Snd(Formula a) => Seq(a, Dot, D(2));
    private static Formula Fr(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Root(Formula a) => Seq(Sqrt, Grp(Call("max", Zero, a)));
    private static Formula Pow(Formula a, Formula exponent) => Seq(Group(a), Caret, Grp(exponent));
    private static Formula Sq(Formula a) => Pow(a, Two);
    private static Formula Negate(Formula a) => Seq(Minus, Group(a));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Both(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Bind(FormulaQuantifier q, string v, Formula t, Formula b) =>
        new Formula.Bind(q, FormulaIdentifier.Create(v), t, b);
    private static Formula All(string v, Formula t, Formula b) => Bind(FormulaQuantifier.ForAll, v, t, b);
    private static Formula Lam(string v, Formula t, Formula b) =>
        Seq(Lambda, Sp, Group(Seq(X(v), Colon, Sp, t)), Comma, Sp, b);
    private static Formula Let(string v, Formula value, Formula b) =>
        Seq(Mathrm, Grp(F.Id("let")), Sp, X(v), Sp, Eq, Sp, value, Comma, Sp, b);
}
