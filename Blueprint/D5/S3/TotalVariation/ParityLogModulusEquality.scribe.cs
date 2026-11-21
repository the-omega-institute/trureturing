using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class ParityLogModulusEqualityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At positive distance, affine parity recovery attains the logarithmic bound exactly below a strict threshold.",
        H("Equality in the logarithmic parity modulus"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("equality-requires-cutoff-and-offset"),
                DeclarationHandle.Create(
                    "D5/S3/TotalVariation/ParityLogModulusEquality.equality_requires_cutoff_and_offset"),
                H("Equality forces the threshold and a common offset"),
                StatementSource.FromAuthor(Necessity()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The input-bit rates are (1-f(i))/2 and (1-g(i))/2. The two laws may start " +
                    "with distinct offsets. At positive distance, equality in strict Jensen " +
                    "forces a common nonzero moment displacement. Scalar equality fixes one " +
                    "magnitude at e and forces the two moments to have the same sign. Equality " +
                    "in the triangle inequality aligns their signed logarithmic differences. " +
                    "Inverting these complementary profiles yields the strict threshold because " +
                    "the target column is present and its factors lie in the open unit interval."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("equality-criterion-sufficient"),
                DeclarationHandle.Create(
                    "D5/S3/TotalVariation/ParityLogModulusEquality.equality_criterion_sufficient"),
                H("The threshold admits an attaining pair"),
                StatementSource.FromAuthor(Sufficiency()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Use one input bit per nonzero group element and use offset zero in both " +
                    "laws. The assigned log bias factors realize the complementary nontrivial " +
                    "moment profiles. Inverting their difference gives a point mass at the " +
                    "target minus the uniform mass, scaled by the common moment displacement. " +
                    "This computes the specified total variation and attains the bound."))),
                DescribeRole.Theorem))));

    private static Formula A => F.Id("A");
    private static Formula I => F.Id("I");
    private static Formula C => F.Id("c");
    private static Formula S => F.Id("s");
    private static Formula T => F.Id("t");
    private static Formula X => F.Id("x");
    private static Formula Y => F.Id("y");
    private static Formula E => F.Id("e");
    private static Formula Target => F.Id("a");
    private static Formula Factors => F.Id("f");
    private static Formula OtherFactors => F.Id("g");
    private static Formula Index => F.Id("i");
    private static Formula Order => F.Id("N");
    private static Formula Measure => F.Id("P");
    private static Formula OtherMeasure => F.Id("Q");
    private static Formula Readout => F.Id("R");
    private static Formula GroupBias => F.Id("G");
    private static Formula Law => F.Id("L");
    private static Formula M => F.Id("m");
    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Characters => Call("AddChar", A, Seq(Mathbb, Grp(F.Id("C"))));
    private static Formula Bias => Arrow(I, Real);

    private static Formula Necessity() => Disp(new Formula.Aligned([
        .. Ambient(),
        Seq(Forall, Sp, Typed(I, Name("Type")), Comma, Instance("Fintype", I), Comma),
        .. Definitions(),
        Seq(Forall, Sp, Typed(C, Arrow(I, A)), Typed(S, A), Typed(T, A), Typed(Target, A),
            Typed(Factors, Bias), Typed(OtherFactors, Bias), Typed(E, Real), Comma),
        Let(Measure, At(Law, C, S, Factors)),
        Let(OtherMeasure, At(Law, C, T, OtherFactors)),
        Let(Delta, Call("TV", Measure, OtherMeasure)),
        Seq(Target, Neq, Sp, D(0), Sp, Land, Sp, Open, Exists, Sp, Typed(Index, I), Comma,
            At(C, Index), Eq, Target, Close, Sp, Land, Sp, D(0), Lt, E, Sp, Land),
        Seq(UnitFactors(Factors), Sp, Land, Sp, UnitFactors(OtherFactors), Sp, Land, Sp, Floor(), Sp, Land),
        Seq(D(0), Lt, Delta, Sp, Land, Sp, Tight(), Sp, Longrightarrow),
        Seq(Cutoff(), Sp, Land, Sp, S, Eq, T)
    ]));

    private static Formula Sufficiency() => Disp(new Formula.Aligned([
        .. Ambient(),
        Let(I, Seq(OpenBrace, X, InMacro, Sp, A, Bar, X, Neq, Sp, D(0), CloseBrace)),
        .. Definitions(),
        Let(C, Seq(X, Sp, Mapsto, Sp, X)),
        Seq(Forall, Sp, Typed(Target, A), Typed(E, Real), Typed(Delta, Real), Comma,
            Target, Neq, Sp, D(0), Sp, Land, Sp, D(0), Lt, E, Sp, Land, Sp, D(0), Lt, Delta,
            Sp, Land, Sp, Cutoff(), Sp, Longrightarrow),
        Seq(Exists, Sp, Typed(Factors, Bias), Typed(OtherFactors, Bias), Comma,
            UnitFactors(Factors), Sp, Land, Sp, UnitFactors(OtherFactors), Sp, Land),
        Let(Measure, At(Law, C, D(0), Factors)),
        Let(OtherMeasure, At(Law, C, D(0), OtherFactors)),
        Seq(Floor(), Sp, Land, Sp, Call("TV", Measure, OtherMeasure), Eq, Delta, Sp, Land),
        Tight()
    ]));

    private static Formula[] Ambient() => [
        Seq(Forall, Sp, Typed(A, Name("Type")), Comma, Instance("AddCommGroup", A),
            Instance("Fintype", A), Comma),
        Let(Order, Abs(A)),
        Seq(Open, Forall, Sp, Typed(X, A), Comma, X, Plus, X, Eq, D(0), Close,
            Sp, Land, Sp, D(1), Lt, Order, Sp, Longrightarrow),
        Let(Beta, Fr(Seq(Order, Minus, D(1)), Order))
    ];

    private static Formula[] Definitions()
    {
        Formula vector = Arrow(I, Name("Bool"));
        Formula component = new Formula.Subscript(X, Index);
        return [
            Let(At(Readout, Typed(C, Arrow(I, A)), Typed(S, A), Typed(X, vector)),
                Seq(S, Plus, new Formula.Subscript(Sum, Index), component, At(C, Index))),
            Let(At(Law, Typed(C, Arrow(I, A)), Typed(S, A), Typed(Factors, Bias)),
                Seq(Y, Mapsto, new Formula.Subscript(Sum, Seq(X, InMacro, Sp, Par(vector),
                    Colon, At(Readout, C, S, X), Eq, Y)), new Formula.Subscript(Prod, Index),
                    Fr(Seq(D(1), Plus, new Formula.Power(Par(Seq(Minus, D(1))), component),
                        At(Factors, Index)), D(2)))),
            Let(At(GroupBias, Typed(C, Arrow(I, A)), Typed(Factors, Bias), Typed(Target, A)),
                Seq(new Formula.Subscript(Prod, Seq(Index, Colon, At(C, Index), Eq, Target)),
                    At(Factors, Index))),
            Let(At(M, Typed(Measure, Arrow(A, Real)), Typed(Psi, Characters)),
                Seq(new Formula.Subscript(Sum, Seq(X, Sp, InMacro, Sp, A)),
                    At(Measure, X), Sp, Re, Sp, At(Psi, X)))
        ];
    }

    private static Formula UnitFactors(Formula factors) =>
        Par(Seq(Forall, Sp, Typed(Index, I), Comma, D(0), Lt, At(factors, Index), Lt, D(1)));
    private static Formula Floor() =>
        Par(Seq(Forall, Sp, Typed(Psi, Characters), Comma, E, Le, Abs(At(M, Measure, Psi)),
            Sp, Land, Sp, E, Le, Abs(At(M, OtherMeasure, Psi))));
    private static Formula Ratio() => Seq(D(1), Plus, Fr(Delta, Seq(Beta, Sp, E)));
    private static Formula Cutoff() =>
        Seq(E, new Formula.Power(Par(Ratio()), Fr(Order, D(2))), Lt, D(1));
    private static Formula Tight() => Seq(
        Abs(Seq(Log, Sp, At(GroupBias, C, Factors, Target), Minus,
            Log, Sp, At(GroupBias, C, OtherFactors, Target))),
        Eq, D(2), Beta, Sp, Log, Sp, Par(Ratio()));

    private static Formula Par(Formula body) => Seq(Open, body, Close);
    private static Formula Abs(Formula body) => new Formula.Absolute(body);
    private static Formula Fr(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Arrow(Formula from, Formula to) => Seq(from, Sp, To, Sp, to);
    private static Formula Typed(Formula variable, Formula type) => Par(Seq(variable, Colon, Sp, type));
    private static Formula Name(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => At(Name(name), args);
    private static Formula Instance(string name, Formula type) =>
        Seq(OpenBracket, Call(name, type), CloseBracket);
    private static Formula Let(Formula lhs, Formula rhs) => Seq(Name("let"), Sp, lhs, Colon, Eq, rhs, Comma);

    private static Formula At(Formula function, params Formula[] args) =>
        Seq(function, Par(Seq(args.SelectMany((argument, index) =>
            index == 0 ? new[] { argument } : new[] { Comma, Sp, argument }).ToArray())));
}
