using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using Fm = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class EpsteinMellinMinimumDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Montgomery =
        LibraryNoteRef.Create("D5/L/Fourier/montgomery1988minimal");
    private static readonly LibraryNoteRef Cassels =
        LibraryNoteRef.Create("D5/L/Fourier/cassels1959rankin");
    private static readonly LibraryNoteRef Rankin =
        LibraryNoteRef.Create("D5/L/Fourier/rankin1953minimum");
    private static readonly LibraryNoteRef EnnolaLemma =
        LibraryNoteRef.Create("D5/L/Fourier/ennola1964lemma");
    private static readonly LibraryNoteRef EnnolaProblem =
        LibraryNoteRef.Create("D5/L/Fourier/ennola1964problem");
    private static readonly LibraryNoteRef Diananda =
        LibraryNoteRef.Create("D5/L/Fourier/diananda1964notes");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For real s greater than one the Epstein series is the Gamma-normalized Mellin " +
        "integral of theta minus one. Hexagonal lattices uniquely minimize it at every " +
        "positive covolume, with the normalized orthogonal-image equality classification.",
        H("Epstein zeta through the theta Mellin integral"), Blocks([.. Section0.Entries()])));

    private static class Section0
    {
        public static DocumentBlock[] Entries() =>
        [
            Entry("epstein", "Planar Epstein zeta series", Definition(),
                "The series uses the positive unit-area binary quadratic form. " +
                "For s greater than one its zero-vector summand is zero. Outside the summability " +
                "range the totalized sum is not an analytic continuation.", true),
            Entry("continuousOn_temperature", "Temperature continuity", TemperatureFormula(),
                "Near any positive temperature t, all summands are bounded by the Gaussian " +
                "at temperature t divided by two. This summable bound makes the sum continuous."),
            Entry("epstein_summable", "Absolute convergence", Summability(),
                "The maximum norm of the integer coordinate vector squared is " +
                "bounded by the sum of the coordinate squares. Gaussian " +
                "quadratic control bounds this sum by a fixed positive constant " +
                "times the form. Taking negative real powers bounds each " +
                "nonzero Epstein term by that constant to the power s times " +
                "the maximum norm to the power negative two s. The latter " +
                "series is summable for two s greater than two."),
            Entry("epstein_mellin_integrable", "Integrability of the Mellin weight", Integrable(),
                "For each nonzero integer pair, the Gamma integral evaluates " +
                "the integral of its Gaussian times t to the power s minus one. " +
                "The resulting positive values are pi to negative s times " +
                "Gamma of s times the Epstein terms. Their sum is finite. " +
                "The integral of the sum of absolute values is finite by " +
                "Tonelli, and bounds the absolute value of the summed function. " +
                "Continuity at every positive t supplies measurability."),
            Entry("epstein_mellin", "Mellin representation", Mellin(),
                "The zero vector contributes exactly one to theta. Removing it " +
                "and interchanging the remaining Gaussian sum with the integral " +
                "is justified by the summable integral norms. The Gamma integral " +
                "and its positivity give the displayed normalization."),
            Entry("reduced_epstein_minimum", "Unique reduced Epstein minimum", Minimum(),
                "Multiply the theta comparison by the positive Mellin weight " +
                "and integrate. If the reduced point differs from the hexagonal " +
                "point, the theta gap is strictly positive at every positive " +
                "temperature. The weighted gap therefore has support containing " +
                "the whole positive half-line, so its integral is strictly " +
                "positive. This proves the classical Epstein minimum and its equality classification."),
            Entry("basisEpstein", "Epstein zeta in actual basis coordinates", BasisDefinition(),
                "The summands are the negative s-th powers of the squared " +
                "lengths of all integer combinations of the two basis vectors.", true),
            Entry("basis_epstein_minimum_isometry", "Epstein minimum and orthogonal rigidity", BasisMinimum(),
                "Normalize a basis of positive covolume A to unit area. Its Epstein series scales by " +
                "A to the power negative s. The unit-area minimum yields the scaled comparison value " +
                "and equality precisely when the normalized basis generates an orthogonal hexagonal " +
                "image. Positive Mellin weights preserve the strict theta gap for every real s " +
                "greater than one.")
        ];

    private static DocumentBlock Entry(string name, string title, Formula formula, string body,
        bool definition = false) => Describe.Lean(
            DescribeId.Create("epstein-mellin-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Fourier/EpsteinMellinMinimum." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), (name is "reduced_epstein_minimum" or "basis_epstein_minimum_isometry"
                ? AssessedProvenance.FromLiterature(Cassels)
                : AssessedProvenance.FromRepo(Montgomery, Cassels, Rankin, EnnolaLemma, EnnolaProblem, Diananda)),
            Blocks(Paragraph(Text(body))),
            definition ? DescribeRole.Definition : DescribeRole.Theorem);
    private static Formula V(string s) => Fm.Id(s);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula C => Seq(Mathbb, Grp(V("C")));
    private static Formula Z => Seq(Mathbb, Grp(V("Z")));
    private static Formula All(string s, Formula t, Formula p) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, p);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Mul(Formula a, Formula b) => Multiply(a, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula NegF(Formula a) => new Formula.Negate(a);
    private static Formula Lam(string s, Formula t, Formula p) =>
        Seq(Open, V(s), Colon, t, Sp, Mapsto, Sp, p, Close);
    private static Formula ForSXY(Formula p) => All("s", R, All("x", R, All("y", R, p)));
    private static Formula Conditions(Formula p) =>
        Imp(Lt(D(1), V("s")), Imp(Lt(D(0), V("y")), p));
    private static Formula Form => Call("Q", V("x"), V("y"), V("v"));
    private static Formula Term => Pow(Form, NegF(V("s")));
    private static Formula Value => Call("epstein", V("s"), V("x"), V("y"));
    private static Formula Half => Div(D(1), D(2));
    private static Formula Height => Div(Call("sqrt", D(3)), D(2));
    private static Formula Hex => Call("epstein", V("s"), Half, Height);
    private static Formula Weight => Mul(Sub(Call("F", V("t"), V("x"), V("y")), D(1)),
        Pow(V("t"), Sub(V("s"), D(1))));
    private static Formula Definition() => ForSXY(Equal(Value,
        Call("tsum", Lam("v", Call("Prod", Z, Z), Term))));
    private static Formula Summability() => ForSXY(Conditions(
        Call("Summable", Lam("v", Call("Prod", Z, Z), Term))));
    private static Formula Integrable() => ForSXY(Conditions(
        Call("IntegrableOn", Lam("t", R, Weight), Call("Ioi", D(0)))));
    private static Formula Mellin() => ForSXY(Conditions(Equal(Value,
        Mul(Div(Pow(Pi, V("s")), Call("Gamma", V("s"))),
            Call("integral", Call("Ioi", D(0)), Lam("t", R, Weight))))));
    private static Formula Minimum() => ForSXY(Imp(Lt(D(1), V("s")),
        Imp(Le(D(0), V("x")), Imp(Le(V("x"), Half), Imp(Le(Height, V("y")),
            And(Le(Hex, Value), Iff(Equal(Value, Hex),
                And(Equal(V("x"), Half), Equal(V("y"), Height)))))))));
    private static Formula ForABS(Formula p) => All("a", C, All("b", C, All("s", R, p)));
    private static Formula Area => Equal(AbsF(Sub(
        Mul(Call("re", V("a")), Call("im", V("b"))),
        Mul(Call("im", V("a")), Call("re", V("b"))))), V("A"));

    private static Formula AbsF(Formula a) => new Formula.Absolute(a);
    private static Formula BasisValue => Call("basisEpstein", V("s"), V("a"), V("b"));
    private static Formula BasisTerm => Pow(Call("normSq", Add(
        Mul(Call("fst", V("v")), V("a")), Mul(Call("snd", V("v")), V("b")))),
        NegF(V("s")));
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula BasisConditions(Formula p) =>
        All("A", R, Imp(Lt(D(0), V("A")), Imp(Area, Imp(Lt(D(1), V("s")), p))));

    private static Formula BasisDefinition() => ForABS(Equal(BasisValue,
        Call("tsum", Lam("v", Call("Prod", Z, Z), BasisTerm))));


    private static Formula BasisMinimum() => ForABS(BasisConditions(
        And(Le(Mul(Pow(V("A"), NegF(V("s"))), Hex), BasisValue),
            Iff(Equal(BasisValue, Mul(Pow(V("A"), NegF(V("s"))), Hex)),
                Call("IsHexagonalBasis", Normalize(V("a")), Normalize(V("b")))))));
    private static Formula Normalize(Formula z) => Call("smul",
        Div(D(1), Call("sqrt", V("A"))), z);

    private static Formula TemperatureFormula() => All("x", R, All("y", R,
        Imp(Lt(D(0), V("y")), Call("ContinuousOn",
            Lam("t", R, Call("F", V("t"), V("x"), V("y"))), Call("Ioi", D(0))))));

    }
}
