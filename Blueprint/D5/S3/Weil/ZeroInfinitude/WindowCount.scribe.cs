using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZeroInfinitude;

internal sealed class WindowCountDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/ZeroInfinitude/WindowCount.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every sufficiently high fixed-width window contains at least a positive multiple "
            + "of log T nontrivial zeta zeros, counted with multiplicity.",
        H("Logarithmic Zero Count in Every Fixed-Width Window"),
        Blocks(
            Paragraph(Text(
                "This is a logarithmic lower bound on the multiplicity-weighted zero count "
                    + "in every fixed-width window at large height. It is obtained from the "
                    + "same cosine-packet explicit-formula estimate as WindowZero by splitting "
                    + "the zero side into the window and its complement.")),
            Paragraph(Text(
                "Together with the frozen local upper bound zetaZeroConfig_local_count, this "
                    + "pins the true order log T of the window count. The constants R, T0, and "
                    + "c-prime are existential absolute constants; no numerical value is claimed.")),
            Paragraph(Text(
                "Nothing is asserted about real parts of the zeros. This is not a proof of the "
                    + "Riemann hypothesis.")),
            Describe.Lean(
                DescribeId.Create("radius-shifted-inverse-square-complement-tail"),
                DeclarationHandle.Create(
                    Prefix + "exists_radius_shifted_inv_sq_tsum_compl"),
                H("One fixed radius controls every shifted complement tail"),
                StatementSource.FromAuthor(ComplementTail()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The frozen finite-subfamily estimate is applied to every finite subset "
                        + "of the window complement. Nonnegativity then yields summability and "
                        + "the same logarithmic tail bound for the full complement series."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-side-norm-window-count"),
                DeclarationHandle.Create(Prefix + "zero_side_norm_le_window_count"),
                H("The zero side splits into a window count and a logarithmic tail"),
                StatementSource.FromAuthor(ZeroSideSplit()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The central negative-frequency window and its conjugate image each have "
                        + "multiplicity sum N(T-R,T+R). The two complement series obey the fixed "
                        + "radius estimate, while closed-strip decay converts both pieces into "
                        + "the stated zero-side norm bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("window-count-lower-log"),
                DeclarationHandle.Create(Prefix + "window_count_lower_log"),
                H("Every large fixed-width window has logarithmically many zeros"),
                StatementSource.FromAuthor(WindowCountLowerLog()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Choose the complement-tail coefficient below the positive logarithmic "
                        + "coefficient in the frozen explicit-formula lower bound. For all large "
                        + "T, the remaining logarithmic mass must be carried by the central "
                        + "multiplicity-weighted window count."))),
                DescribeRole.Theorem))));

    private static Formula ComplementTail()
    {
        Formula iota = F.Id("iota");
        Formula gamma = F.Id("gamma");
        Formula multiplicity = F.Id("m");
        Formula a0 = F.Id("A0");
        Formula epsilon = F.Id("epsilon");
        Formula radius = F.Id("R");
        Formula t = F.Id("T");
        Formula s = F.Id("s");
        Formula rho = F.Id("rho");
        Formula displacement = Subtract(Apply(gamma, rho), t);
        Formula summand = new Formula.Fraction(
            Apply(multiplicity, rho),
            Add(D(1), new Formula.Power(Parenthesize(displacement), D(2))));
        Formula complement = new Formula.SetBuilder(
            NotMember(rho, s), rho, iota);
        Formula tail = Tsum(rho, complement, summand);
        Formula gap = ForAll(
            [Bound("rho", iota)],
            Implies(
                NotMember(rho, s),
                LessEqual(radius, new Formula.Absolute(displacement))));
        Formula estimate = LessEqual(
            tail,
            Multiply(
                Multiply(D(4), a0),
                Add(
                    Multiply(epsilon, NaturalLog(Add(new Formula.Absolute(t), D(3)))),
                    F.Id("totalWeight"))));
        Formula conclusion = Exists(
            [Bound("R", Reals())],
            All(
                LessEqual(D(2), radius),
                ForAll(
                    [Bound("T", Reals()), Bound("s", Call("Finset", iota))],
                    Implies(
                        gap,
                        All(
                            Call("Summable", Lambda(rho, complement, summand)),
                            estimate)))));

        return Disp(ForAll(
            [
                Bound("iota", F.Id("Type")),
                Bound("gamma", new Formula.TypeArrow(iota, Reals())),
                Bound("m", new Formula.TypeArrow(iota, Naturals())),
                Bound("A0", Reals()),
                Bound("epsilon", Reals()),
            ],
            Implies(
                All(
                    Call("LocalCount", gamma, multiplicity, a0),
                    Less(D(0), epsilon)),
                conclusion)));
    }

    private static Formula ZeroSideSplit()
    {
        Formula k = F.Id("K");
        Formula a0 = F.Id("A0");
        Formula epsilon = F.Id("epsilon");
        Formula radius = F.Id("R");
        Formula t = F.Id("T");
        Formula z = F.Id("z");
        Formula rho = F.Id("rho");
        Formula carrier = Carrier();
        Formula packetSquare = F.Id("packetSquare");
        Formula packet = Call("cosineModulation", packetSquare, t);
        Formula zeroSummand = Multiply(
            Call("mult", F.Id("zetaZeroConfig"), rho),
            Call("paperFT", packet, Call("gammaOf", rho)));
        Formula zeroSide = Tsum(rho, carrier, zeroSummand);
        Formula strip = LessEqual(
            new Formula.Absolute(Call("Im", z)),
            new Formula.Fraction(D(1), D(2)));
        Formula decayBound = LessEqual(
            new Formula.Norm(Call("paperFT", packetSquare, z)),
            new Formula.Fraction(
                k,
                Add(D(1), new Formula.Power(
                    Parenthesize(Call("Re", z)), D(2)))));
        Formula decay = ForAll(
            [Bound("z", Complexes())],
            Implies(strip, decayBound));
        Formula ordinate = Lambda(rho, carrier, Call("Im", rho));
        Formula multiplicity = Lambda(
            rho, carrier, Call("mult", F.Id("zetaZeroConfig"), rho));
        Formula count = Call(
            "N", F.Id("zetaZeroConfig"), Subtract(t, radius), Add(t, radius));
        Formula tail = Multiply(
            Multiply(Multiply(D(4), k), a0),
            Add(
                Multiply(epsilon, NaturalLog(Add(t, D(3)))),
                F.Id("totalWeight")));
        Formula estimate = LessEqual(
            new Formula.Norm(zeroSide),
            Add(Multiply(k, count), tail));
        Formula conclusion = Exists(
            [Bound("R", Reals())],
            All(
                LessEqual(D(2), radius),
                ForAll(
                    [Bound("T", Reals())],
                    Implies(LessEqual(D(0), t), estimate))));

        return Disp(ForAll(
            [Bound("K", Reals()), Bound("A0", Reals()), Bound("epsilon", Reals())],
            Implies(
                All(
                    LessEqual(D(0), k),
                    decay,
                    Call("LocalCount", ordinate, multiplicity, a0),
                    Less(D(0), epsilon)),
                conclusion)));
    }

    private static Formula WindowCountLowerLog()
    {
        Formula radius = F.Id("R");
        Formula t0 = new Formula.Subscript(F.Id("T"), D(0));
        Formula cprime = Seq(F.Id("c"), Apos);
        Formula t = F.Id("T");
        Formula count = Call(
            "N", F.Id("zetaZeroConfig"), Subtract(t, radius), Add(t, radius));
        Formula lower = Multiply(cprime, NaturalLog(Add(t, D(3))));

        return Disp(Seq(
            F.Exists, Sp, radius, Comma, Sp, t0, Comma, Sp, cprime,
            Sp, InMacro, Sp, Reals(), Comma, Esc,
            D(0), Sp, Lt, Sp, radius, Sp, Land, Sp,
            D(0), Sp, Lt, Sp, cprime, Sp, Land, Sp,
            Forall, Sp, t, Sp, InMacro, Sp, Reals(), Comma, Esc,
            t0, Sp, Leq, Sp, t, Sp, Rightarrow, Sp,
            lower, Sp, Leq, Sp, count));
    }

    private static Formula Carrier() =>
        Call("carrier", F.Id("zetaZeroConfig"));

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula NaturalLog(Formula argument) =>
        Seq(Log, Open, argument, Close);

    private static Formula Parenthesize(Formula formula) =>
        Seq(Open, formula, Close);

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula Lambda(Formula variable, Formula domain, Formula body) =>
        Seq(Open, variable, Colon, Sp, domain, Sp, Mapsto, Sp, body, Close);

    private static Formula Tsum(Formula variable, Formula domain, Formula body) =>
        Seq(Sum, Underscore, Grp(variable, Sp, InMacro, Sp, domain), Sp, body);

    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);

    private static Formula NotMember(Formula value, Formula set) =>
        new Formula.Not(Member(value, set));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Exists(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);

    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = new Formula.Logic(clauses[index], FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
}
