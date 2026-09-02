using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Toroidal;

internal sealed class GoldenToroidalIndexExtensionDocument
    : IScribeDocumentDefinition
{
    private const string ExtensionDeclaration =
        "D5/S3/Analytic/Toroidal/GoldenToroidalIndexExtension."
            + "golden_toroidal_index_extension";

    private const string TemperednessDeclaration =
        "D5/S3/Analytic/Toroidal/GoldenToroidalIndexExtension."
            + "golden_toroidal_temperedness_rhs_iff";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A golden toroidal channel preserves pointwise nonvanishing, the window "
            + "common-zero locus, and the frozen RH temperedness condition.",
        H("Golden Toroidal Index Extension"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-toroidal-index-extension"),
                DeclarationHandle.Create(ExtensionDeclaration),
                H("The golden channel preserves nonvanishing and common zeros"),
                StatementSource.FromAuthor(ExtensionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The original period family P factors pointwise as xiReading times "
                            + "the twist family T. Every point of Omega has an original twist "
                            + "chart with nonzero value. The added pair Pg and Tg is arbitrary "
                            + "apart from the same xiReading factorization.")),
                    Paragraph(Text(
                        "The displayed Sum extension uses the original family on Index and "
                            + "the constant golden family on Unit. Its nonvanishing witness is "
                            + "the injected original witness. Applying the frozen toroidal "
                            + "common-zero theorem to both families identifies their window "
                            + "loci through the same xiReading zero set."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-toroidal-temperedness-rhs-iff"),
                DeclarationHandle.Create(TemperednessDeclaration),
                H("The frozen RH right-hand predicate is extension-invariant"),
                StatementSource.FromAuthor(TemperednessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Global pointwise nonvanishing of T also supplies global "
                            + "nonvanishing of the Sum extension. The frozen toroidal "
                            + "temperedness theorem equates each displayed right-hand "
                            + "predicate with the identical strip-native RH left side, so the "
                            + "two predicates are equivalent.")),
                    Paragraph(Text(
                        "No Euler-germ nonvanishing, O-5 factorization, or identification of "
                            + "Tg with an Euler germ or Zqc is asserted. The result does not "
                            + "strengthen RH and does not use o5_independence."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula MemberOf(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Product(Formula left, Formula right) =>
        Seq(left, Sp, Times, Sp, right);

    private static Formula SumElim(Formula original, Formula golden) =>
        Apply(
            Seq(F.Id("Sum"), Dot, F.Id("elim")),
            original,
            Call("const", golden));

    private static Formula ExtensionFormula()
    {
        Formula type = Call("Type");
        Formula complex = Call("Complex");
        Formula unitType = Call("Unit");
        Formula indexType = F.Id("Index");
        Formula omega = F.Id("Omega");
        Formula period = F.Id("P");
        Formula twist = F.Id("T");
        Formula goldenPeriod = F.Id("Pg");
        Formula goldenTwist = F.Id("Tg");
        Formula index = F.Id("i");
        Formula extendedIndex = F.Id("j");
        Formula point = F.Id("s");
        Formula subtypePoint = F.Id("x");
        Formula pointValue = Call("val", subtypePoint);
        Formula familyType = Arrow(indexType, Arrow(complex, complex));
        Formula functionType = Arrow(complex, complex);
        Formula sumIndexType = Call("Sum", indexType, unitType);
        Formula omegaSubtype = Call("Subtype", omega);

        Formula At(Formula family, Formula i, Formula s) =>
            Apply(Apply(family, i), s);
        Formula extendedPeriodAt(Formula i, Formula s) =>
            Apply(Apply(SumElim(period, goldenPeriod), i), s);
        Formula extendedTwistAt(Formula i, Formula s) =>
            Apply(Apply(SumElim(twist, goldenTwist), i), s);

        Formula factorization = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", indexType), Bound("s", complex)],
            EqualTo(
                At(period, index, point),
                Product(
                    Apply(F.Id("xiReading"), point),
                    At(twist, index, point))));
        Formula pointwiseNonvanishing = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            Implies(
                MemberOf(point, omega),
                new Formula.BindMany(
                    FormulaQuantifier.Exists,
                    [Bound("i", indexType)],
                    NotEqualTo(At(twist, index, point), D(0)))));
        Formula goldenFactorization = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            EqualTo(
                Apply(goldenPeriod, point),
                Product(
                    Apply(F.Id("xiReading"), point),
                    Apply(goldenTwist, point))));
        Formula hypotheses = And(
            factorization,
            And(pointwiseNonvanishing, goldenFactorization));

        Formula extendedNonvanishing = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            Implies(
                MemberOf(point, omega),
                new Formula.BindMany(
                    FormulaQuantifier.Exists,
                    [Bound("j", sumIndexType)],
                    NotEqualTo(extendedTwistAt(extendedIndex, point), D(0)))));
        Formula extendedAllZero = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("j", sumIndexType)],
            EqualTo(extendedPeriodAt(extendedIndex, pointValue), D(0)));
        Formula originalAllZero = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", indexType)],
            EqualTo(At(period, index, pointValue), D(0)));
        Formula locusEquality = EqualTo(
            new Formula.SetBuilder(extendedAllZero, subtypePoint, omegaSubtype),
            new Formula.SetBuilder(originalAllZero, subtypePoint, omegaSubtype));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("Index", type),
                Bound("Omega", Call("Set", complex)),
                Bound("P", familyType),
                Bound("T", familyType),
                Bound("Pg", functionType),
                Bound("Tg", functionType),
            ],
            Implies(hypotheses, And(extendedNonvanishing, locusEquality))));
    }

    private static Formula TemperednessFormula()
    {
        Formula type = Call("Type");
        Formula complex = Call("Complex");
        Formula unitType = Call("Unit");
        Formula indexType = F.Id("Index");
        Formula twist = F.Id("T");
        Formula goldenTwist = F.Id("Tg");
        Formula point = F.Id("s");
        Formula index = F.Id("i");
        Formula extendedIndex = F.Id("j");
        Formula sumIndexType = Call("Sum", indexType, unitType);
        Formula half = new Formula.Fraction(D(1), D(2));
        Formula familyType = Arrow(indexType, Arrow(complex, complex));
        Formula functionType = Arrow(complex, complex);

        Formula twistAt(Formula i, Formula s) => Apply(Apply(twist, i), s);
        Formula extendedTwistAt(Formula i, Formula s) =>
            Apply(Apply(SumElim(twist, goldenTwist), i), s);
        Formula temperedAt(Formula s) => EqualTo(
            Call("Re", Seq(s, Sp, Minus, Sp, half)),
            D(0));

        Formula pointwiseNonvanishing = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            new Formula.BindMany(
                FormulaQuantifier.Exists,
                [Bound("i", indexType)],
                NotEqualTo(twistAt(index, point), D(0))));
        Formula extendedInvisible = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("j", sumIndexType)],
            EqualTo(
                Product(
                    Call("completedRiemannZeta", point),
                    extendedTwistAt(extendedIndex, point)),
                D(0)));
        Formula originalInvisible = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", indexType)],
            EqualTo(
                Product(
                    Call("completedRiemannZeta", point),
                    twistAt(index, point)),
                D(0)));
        Formula extendedPredicate = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            Implies(extendedInvisible, temperedAt(point)));
        Formula originalPredicate = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            Implies(originalInvisible, temperedAt(point)));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("Index", type),
                Bound("T", familyType),
                Bound("Tg", functionType),
            ],
            Implies(
                pointwiseNonvanishing,
                Iff(extendedPredicate, originalPredicate))));
    }
}
