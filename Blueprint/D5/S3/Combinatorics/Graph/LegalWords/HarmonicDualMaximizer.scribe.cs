using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.LegalWords;

internal sealed class HarmonicDualMaximizerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/LegalWords/HarmonicDualMaximizer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive stationary harmonic-dual masses on independent configurations have uniform "
        + "bounds along every legal addition. Base degree at most three gives a unique positive maximum.",
        H("Parallel flips and harmonic-dual maximizers"),
        Blocks(
            Paragraph(Text(
                "Let H be a finite simple graph. Configurations are the existing independent "
                + "subsets of its vertex set. A legal edge toggles exactly one vertex, using "
                + "symmetric difference with a singleton. The mass function is defined on all "
                + "finite subsets; probabilities assign zero to nonindependent subsets. "
                + "Every degree in the bounds below is a degree in H, not in the graph of configurations.")),
            Describe.Lean(DescribeId.Create("coordinate-load"),
                DeclarationHandle.Create(Prefix + "coordinateLoad"), H("Derivative load"),
                StatementSource.FromAuthor(LoadFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The load at S sums the squared share nu(T)/(nu(S)+nu(T)) over every legal "
                    + "toggle T. Deletion edges and addition edges both occur."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("harmonic-dual"),
                DeclarationHandle.Create(Prefix + "harmonicDual"), H("Harmonic edge objective"),
                StatementSource.FromAuthor(DualFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The directed sum counts each legal edge twice. Division by two recovers "
                    + "the sum over unordered edges. Real division gives zero when both masses are zero."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("regularized-dual"),
                DeclarationHandle.Create(Prefix + "regularizedDual"), H("Square-root regularization"),
                StatementSource.FromAuthor(RegularizedFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The regularizer sums square roots over independent configurations only."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("probabilities"),
                DeclarationHandle.Create(Prefix + "probabilities"), H("Actual probability domain"),
                StatementSource.FromAuthor(ProbabilitiesFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The ordinary finite probability simplex is intersected with the coordinate "
                    + "hyperplanes that set all illegal configuration masses to zero."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("stationary-ratios"),
                DeclarationHandle.Create(Prefix + "stationary_ratio_bounds"),
                H("Bounds for every positive stationary mass"),
                StatementSource.FromAuthor(StationaryFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "No normalization is needed for this statement. Epsilon may be zero. "
                    + "The same stationary equation holds at every independent configuration. "
                    + "Fix an added vertex i and compare ratios on all parallel legal edges. "
                    + "A toggle at j different from i survives the insertion of i exactly when "
                    + "it was legal before and i is not adjacent to j. This includes every deletion.")),
                    Paragraph(Text(
                        "At a largest ratio greater than one, paired contributions and all lost "
                        + "edges force the load difference to be negative, whereas stationarity "
                        + "makes it nonnegative. Thus all legal additions decrease mass. At a "
                        + "smallest ratio, paired contributions reverse direction. Each lost edge "
                        + "costs at most one quarter, and there are at most degree(i) such edges. "
                        + "The resulting lower bound is positive when degree(i) is at most three. "
                        + "For a path, degree at most two gives the numerical lower bound one third."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("regularized-maximum"),
                DeclarationHandle.Create(Prefix + "regularized_maximum"),
                H("A positive regularized maximizer with uniform ratios"),
                StatementSource.FromAuthor(MaximumFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive epsilon the continuous objective attains a maximum on "
                    + "the compact probability domain. If a legal coordinate has zero mass, "
                    + "mixing in a small point mass gains a square-root term while losing only "
                    + "a linear term. Hence the maximizing mass is positive at every legal coordinate. "
                    + "Coordinate exchanges preserve the simplex locally; their zero derivatives "
                    + "give the common stationary value. The parallel-flip bounds then apply.")),
                    Paragraph(Text(
                        "The ratio bounds are independent of epsilon."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("unique-positive-maximum"),
                DeclarationHandle.Create(Prefix + "unique_positive_maximum"),
                H("Unique positive unregularized maximum"),
                StatementSource.FromAuthor(UniqueFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume every degree of the base graph is at most three. Impose the ratio "
                    + "bounds in their linear form on the compact probability domain. "
                    + "All positive regularized maximizers lie in this closed subset. "
                    + "The upper bounds make the empty-set mass maximal. Its mass is positive "
                    + "by normalization, and the strictly positive lower factors propagate "
                    + "positivity along insertions to every independent configuration.")),
                    Paragraph(Text(
                        "Maximize the unregularized objective on this compact subset. "
                        + "The square-root sum is bounded by the number of configurations. "
                        + "Comparison with positive regularized maxima at arbitrarily small "
                        + "epsilon shows that this maximum is global.")),
                    Paragraph(Text(
                        "At a positive maximum the derivative loads are equal. The supporting "
                        + "linear bound for each harmonic edge has equality exactly when the "
                        + "two endpoint mass ratios agree. Equality of the total values forces "
                        + "equality on every edge, even if a competing maximum has zero masses. "
                        + "Deletion paths connect every independent configuration to the empty "
                        + "set; normalization then identifies the two probability vectors.")),
                    Paragraph(Text(
                        "The theorem uses independent subsets. A formulation on admissible "
                        + "Boolean words additionally needs the support bijection and the "
                        + "identification of singleton toggles with Hamming-one edges."))), DescribeRole.Theorem),
            Paragraph(Text(
                "The parallel-flip comparison is a derivation from the independent-set model. "
                + "Finite compactness, differentiation and elementary inequalities are supplied "
                + "by Mathlib. The source status is repo-derived; no claim of literature novelty "
                + "or a general duality theorem is made.")))));

    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Some(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Real() => Call("Real");
    private static Formula V() => F.Id("V");
    private static Formula Hh() => F.Id("H");
    private static Formula Sets() => Call("Finset", V());
    private static Formula Mass() => new Formula.TypeArrow(Sets(), Real());
    private static Formula Nu(Formula s) => Call("nu", s);
    private static Formula Independent(Formula s) => Call("IsIndepSet", Hh(), s);
    private static Formula Insert(Formula s, Formula i) => Call("insert", i, s);
    private static Formula Flip(Formula s, Formula i) => Call("symmDiff", s, Seq(OpenBrace, i, CloseBrace));
    private static Formula Load(Formula s) => Call("coordinateLoad", Hh(), F.Id("nu"), s);
    private static Formula Reg() => Call("regularizedDual", Hh(), F.Id("e"), F.Id("nu"));
    private static Formula Configs() => Call("configurations", Hh(), Call("univ", V()));
    private static Formula Domain() => Call("probabilities", Hh());
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Not(Formula a) => Seq(Neg, Sp, a);
    private static Formula Instance(Formula t, Formula b) => Seq(OpenBracket, t, CloseBracket, Sp, b);
    private static Formula Graph(Formula b) => All("V", Call("Type"), Instance(Call("Fintype", V()),
        Instance(Call("DecidableEq", V()), All("H", Call("SimpleGraph", V()),
            Instance(Call("DecidableRel", Call("Adj", Hh())), b)))));
    private static Formula SumOver(string n, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(F.Sum, Seq(F.Id(n), Sp, InMacro, Sp, domain)), Sp,
            Seq(Open, body, Close));
    private static Formula Positive() => All("S", Sets(), Imp(Independent(F.Id("S")), Lt(D(0), Nu(F.Id("S")))));
    private static Formula Stationary() => All("S", Sets(), Imp(Independent(F.Id("S")),
        Eq(Add(Load(F.Id("S")), Div(F.Id("e"), Mul(D(2), Call("sqrt", Nu(F.Id("S")))))), F.Id("t"))));
    private static Formula Ratios() => All("i", V(), All("S", Sets(),
        Imp(And(Not(Member(F.Id("i"), F.Id("S"))), Independent(Insert(F.Id("S"), F.Id("i")))),
            And(Le(Div(Sub(D(4), Call("degree", Hh(), F.Id("i"))),
                    Add(D(4), Call("degree", Hh(), F.Id("i")))),
                Div(Nu(Insert(F.Id("S"), F.Id("i"))), Nu(F.Id("S")))),
                Le(Div(Nu(Insert(F.Id("S"), F.Id("i"))), Nu(F.Id("S"))), D(1))))));
    private static Formula LoadFormula() => Disp(Graph(All("nu", Mass(), All("S", Sets(),
        Eq(Load(F.Id("S")), SumOver("j", Call("univ", V()),
            Call("ite", Independent(Flip(F.Id("S"), F.Id("j"))),
                new Formula.Power(Div(Nu(Flip(F.Id("S"), F.Id("j"))),
                    Add(Nu(F.Id("S")), Nu(Flip(F.Id("S"), F.Id("j"))))), D(2)), D(0))))))));
    private static Formula DualFormula() => Disp(Graph(All("nu", Mass(),
        Eq(Call("harmonicDual", Hh(), F.Id("nu")), Div(SumOver("S", Configs(),
            SumOver("i", Call("univ", V()), Call("ite", Independent(Flip(F.Id("S"), F.Id("i"))),
                Div(Mul(Nu(F.Id("S")), Nu(Flip(F.Id("S"), F.Id("i")))),
                    Add(Nu(F.Id("S")), Nu(Flip(F.Id("S"), F.Id("i"))))), D(0)))), D(2))))));
    private static Formula RegularizedFormula() => Disp(Graph(All("e", Real(), All("nu", Mass(),
        Eq(Reg(), Add(Call("harmonicDual", Hh(), F.Id("nu")),
            Mul(F.Id("e"), SumOver("S", Configs(), Call("sqrt", Nu(F.Id("S")))))))))));
    private static Formula ProbabilitiesFormula() => Disp(Graph(All("nu", Mass(),
        new Formula.Logic(Member(F.Id("nu"), Domain()), FormulaLogicOperator.Iff,
            And(Member(F.Id("nu"), Call("stdSimplex", Real(), Sets())),
                All("S", Sets(), Imp(Not(Independent(F.Id("S"))), Eq(Nu(F.Id("S")), D(0)))))))));
    private static Formula StationaryFormula() => Disp(Graph(All("nu", Mass(), All("e", Real(), All("t", Real(),
        Imp(And(Le(D(0), F.Id("e")), And(Positive(), Stationary())), Ratios()))))));
    private static Formula UniqueFormula() => Disp(Graph(Imp(
        All("i", V(), Le(Call("degree", Hh(), F.Id("i")), D(3))),
        Some("nu", Mass(), And(Member(F.Id("nu"), Domain()),
            And(Call("IsMaxOn", Call("harmonicDual", Hh()), Domain(), F.Id("nu")),
                And(Positive(), And(Ratios(), All("mu", Mass(),
                    Imp(And(Member(F.Id("mu"), Domain()),
                            Call("IsMaxOn", Call("harmonicDual", Hh()), Domain(), F.Id("mu"))),
                        Eq(F.Id("mu"), F.Id("nu"))))))))))));
    private static Formula MaximumFormula() => Disp(Graph(All("e", Real(), Imp(Lt(D(0), F.Id("e")),
        Some("nu", Mass(), And(Member(F.Id("nu"), Domain()),
            And(Call("IsMaxOn", Call("regularizedDual", Hh(), F.Id("e")), Domain(), F.Id("nu")),
                And(Positive(), Ratios()))))))));
}
