using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZeroInfinitude;

internal sealed class WindowZeroDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/ZeroInfinitude/WindowZero.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every sufficiently high window of one fixed width contains a nontrivial zeta zero.",
        H("A Nontrivial Zero in Every Fixed-Width Window"),
        Blocks(
            Paragraph(Text(
                "This is a quantitative zero-distribution statement. The frozen unconditional "
                    + "explicit formula along the cosine packet gives the logarithmic lower bound, "
                    + "while the frozen local zero-count upper bound controls the zero-side tail. "
                    + "Together they show that every window of fixed width 2R at height T at least "
                    + "T0 contains a nontrivial zero.")),
            Paragraph(Text(
                "The constants R and T0 are existential absolute constants determined by the "
                    + "proof's constants; no numerical value is claimed. Nothing is asserted about "
                    + "the real parts of these zeros. This is not a proof of the Riemann hypothesis.")),
            Paragraph(Text(
                "The resulting fixed-width statement is weaker than the classical Littlewood gap "
                    + "bound, but its proof is closed inside this repository.")),
            Describe.Lean(
                DescribeId.Create("literature-rhs-real-lower-log"),
                DeclarationHandle.Create(Prefix + "literatureRHS_re_lower_log"),
                H("The explicit-formula right side has a logarithmic lower bound"),
                StatementSource.FromAuthor(LiteratureRhsLowerLog()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The Archimedean packet contribution supplies a positive multiple of log(T+3). "
                        + "The two pole evaluations vanish and the fixed-support prime contribution "
                        + "is uniformly bounded, so all remaining terms enter one constant M."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exists-radius-shifted-inverse-square-tsum"),
                DeclarationHandle.Create(Prefix + "exists_radius_shifted_inv_sq_tsum"),
                H("A fixed gap radius makes the shifted zero tail small"),
                StatementSource.FromAuthor(ShiftedInverseSquareTail()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive epsilon, unit-window grouping and the local count bound "
                        + "select one radius R at least two. Under an R-gap, the full nonnegative "
                        + "multiplicity-weighted inverse-square series is summable and its logarithmic "
                        + "coefficient is at most 4 A0 epsilon."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exists-zero-near-every-large-height"),
                DeclarationHandle.Create(Prefix + "exists_zero_near_every_large_height"),
                H("Every sufficiently high fixed-width window contains a zero"),
                StatementSource.FromAuthor(WindowConclusion()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Choose epsilon from the positive logarithmic coefficient and the frozen decay "
                        + "and local-count constants. A zero-free window would then force the zero "
                        + "side below half the logarithmic growth of the explicit-formula right side, "
                        + "contradicting their unconditional equality."))),
                DescribeRole.Theorem))));

    private static Formula LiteratureRhsLowerLog()
    {
        Formula c = F.Id("c");
        Formula m = F.Id("M");
        Formula t0 = F.Id("T1");
        Formula t = F.Id("T");
        Formula packet = Call("cosineModulation", F.Id("packetSquare"), t);
        Formula rhs = RealPart(Call("literatureRHS", packet));
        Formula lower = Subtract(
            Multiply(c, NaturalLog(Add(t, D(3)))),
            m);

        return Disp(ExistsMany(
            [Bound("c", Reals()), Bound("M", Reals()), Bound("T1", Reals())],
            And(
                Less(D(0), c),
                ForAllMany(
                    [Bound("T", Reals())],
                    Implies(
                        LessEqual(t0, t),
                        LessEqual(lower, rhs))))));
    }

    private static Formula ShiftedInverseSquareTail()
    {
        Formula iota = F.Id("iota");
        Formula gamma = F.Id("gamma");
        Formula multiplicity = F.Id("m");
        Formula a0 = F.Id("A0");
        Formula epsilon = F.Id("epsilon");
        Formula radius = F.Id("R");
        Formula t = F.Id("T");
        Formula rho = F.Id("rho");
        Formula displacement = Subtract(Apply(gamma, rho), t);
        Formula summand = new Formula.Fraction(
            Apply(multiplicity, rho),
            Add(D(1), new Formula.Power(Parenthesize(displacement), D(2))));
        Formula tail = Tsum(rho, iota, summand);
        Formula gap = ForAllMany(
            [Bound("rho", iota)],
            LessEqual(radius, new Formula.Absolute(displacement)));
        Formula estimate = LessEqual(
            tail,
            Multiply(
                Multiply(D(4), a0),
                Add(
                    Multiply(epsilon, NaturalLog(Add(new Formula.Absolute(t), D(3)))),
                    F.Id("totalWeight"))));
        Formula atT = Implies(
            gap,
            And(Call("Summable", Lambda(rho, iota, summand)), estimate));
        Formula conclusion = ExistsMany(
            [Bound("R", Reals())],
            And(
                LessEqual(D(2), radius),
                ForAllMany([Bound("T", Reals())], atT)));

        return Disp(ForAllMany(
            [
                Bound("iota", F.Id("Type")),
                Bound("gamma", new Formula.TypeArrow(iota, Reals())),
                Bound("m", new Formula.TypeArrow(iota, Naturals())),
                Bound("A0", Reals()),
                Bound("epsilon", Reals()),
            ],
            Implies(
                And(
                    Call("LocalCount", gamma, multiplicity, a0),
                    Less(D(0), epsilon)),
                conclusion)));
    }

    private static Formula WindowConclusion()
    {
        Formula radius = F.Id("R");
        Formula t0 = F.Id("T0");
        Formula t = F.Id("T");
        Formula rho = F.Id("rho");
        Formula carrier = Call("carrier", F.Id("zetaZeroConfig"));
        Formula near = LessEqual(
            new Formula.Absolute(Subtract(Call("Im", rho), t)),
            radius);
        Formula zero = ExistsMany(
            [Bound("rho", carrier)],
            near);

        return Disp(ExistsMany(
            [Bound("R", Reals()), Bound("T0", Reals())],
            And(
                Less(D(0), radius),
                ForAllMany(
                    [Bound("T", Reals())],
                    Implies(LessEqual(t0, t), zero)))));
    }

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula NaturalLog(Formula argument) =>
        Seq(Log, Open, argument, Close);

    private static Formula RealPart(Formula argument) =>
        Seq(Re, Open, argument, Close);

    private static Formula Parenthesize(Formula formula) =>
        Seq(Open, formula, Close);

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula Lambda(Formula variable, Formula domain, Formula body) =>
        Seq(Open, variable, Colon, Sp, domain, Sp, Mapsto, Sp, body, Close);

    private static Formula Tsum(Formula variable, Formula domain, Formula body) =>
        Seq(Sum, Underscore, Grp(variable, Sp, InMacro, Sp, domain), Sp, body);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAllMany(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula ExistsMany(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
}
