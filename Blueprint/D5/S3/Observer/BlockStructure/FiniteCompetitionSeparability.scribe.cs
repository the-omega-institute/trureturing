using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.BlockStructure;

internal sealed class FiniteCompetitionSeparabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite symmetric competitors admit a positive common-denominator feature margin.",
        H("Finite Competition Separability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-symmetric-competitors-have-positive-feature-margin"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/BlockStructure/FiniteCompetitionSeparability."
                        + "finite_competition_separability"),
                H("Finite character depth separates every finite competitor family"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The scale family, every external depth, and the finite orbit family "
                            + "are public inputs. The sign and conjugation exclusions state the "
                            + "orbit quotient directly, without introducing a proxy quotient.")),
                    Paragraph(Text(
                        "The supplied scales construct the common denominator. Its disk bounds "
                            + "exclude unit-circle poles, while the finite-point premise keeps "
                            + "each displayed rational profile defined at every competitor.")),
                    Paragraph(Text(
                        "An even polynomial with every competing orbit as a root gives a real-"
                            + "linear functional that vanishes on the competitor span but not "
                            + "on the target profile. Closedness of the finite span then makes "
                            + "the displayed distance strictly positive."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula scaleCount = F.Id("q");
        Formula competitorCount = F.Id("m");
        Formula scale = F.Id("r");
        Formula scaleDepth = F.Id("N");
        Formula point = F.Id("z");
        Formula referenceDepth = F.Id("d");
        Formula factor = F.Id("f");
        Formula denominator = F.Id("D");
        Formula numerator = F.Id("p");
        Formula feature = Phi;
        Formula competitorSpace = F.Id("W");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula k = F.Id("k");
        Formula w = F.Id("w");
        Formula finScale = Call("Fin", scaleCount);
        Formula finPoint = Call("Fin", Add(competitorCount, D(1)));
        Formula finCompetitor = Call("Fin", competitorCount);
        Formula index = Call("Fin", Add(referenceDepth, D(1)));
        Formula polynomial = Call("Polynomial", complex);
        Formula vector = Arrow(index, complex);

        Formula scaleAtI = Apply(scale, i);
        Formula depthAtI = Apply(scaleDepth, i);
        Formula pointAtI = Apply(point, i);
        Formula pointAtJ = Apply(point, j);
        Formula scaleFactor = Add(
            D(1),
            Mul(Call("C", Call("ofReal", scaleAtI)), F.Id("X")));
        Formula rawDenominator = Call(
            "prod",
            finScale,
            Lambda(
                Typed(i, finScale),
                Call("pow", scaleFactor, Add(depthAtI, D(1)))));

        Formula scaleInDisk = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", finScale)],
            Less(Call("abs", scaleAtI), D(1)));
        Formula orbitExclusions = And(
            NotEqual(pointAtI, pointAtJ),
            And(
                NotEqual(pointAtI, Call("neg", pointAtJ)),
                And(
                    NotEqual(pointAtI, Call("conj", pointAtJ)),
                    NotEqual(pointAtI, Call("neg", Call("conj", pointAtJ))))));
        Formula orbitDistinct = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", finPoint), Bound("j", finPoint)],
            Implies(NotEqual(i, j), orbitExclusions));
        Formula noPole = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("j", finPoint)],
            NotEqual(Call("eval", rawDenominator, pointAtJ), D(0)));

        Formula factorDefinition = Seq(
            Typed(factor, Arrow(finScale, polynomial)), Comma, Sp,
            Forall, Sp, Typed(i, finScale), Comma, Sp,
            Apply(factor, i), Sp, Eq, Sp,
            Add(
                D(1),
                Mul(Call("C", Call("ofReal", scaleAtI)), F.Id("X"))));
        Formula denominatorDefinition = Seq(
            Typed(denominator, polynomial), Sp, Eq, Sp,
            Call(
                "prod",
                finScale,
                Lambda(
                    Typed(i, finScale),
                    Call("pow", Apply(factor, i), Add(depthAtI, D(1))))));
        Formula numeratorDefinition = Seq(
            Typed(numerator, Arrow(index, polynomial)), Comma, Sp,
            Forall, Sp, Typed(k, index), Comma, Sp,
            Apply(numerator, k), Sp, Eq, Sp,
            Mul(
                denominator,
                Call("pow", F.Id("X"), Mul(D(2), k))));
        Formula featureDefinition = Seq(
            Typed(feature, Arrow(complex, vector)), Comma, Sp,
            Forall, Sp, Typed(w, complex), Comma, Sp, Typed(k, index), Comma, Sp,
            Apply(Apply(feature, w), k), Sp, Eq, Sp,
            new Formula.Fraction(
                Call("eval", Apply(numerator, k), w),
                Call("eval", denominator, w)));
        Formula competitorDefinition = Seq(
            Typed(competitorSpace, Call("Submodule", real, vector)), Sp, Eq, Sp,
            Call(
                "span",
                real,
                Call(
                    "range",
                    Lambda(
                        Typed(j, finCompetitor),
                        Apply(feature, Apply(point, Call("succ", j)))))));
        Formula letObjects = Seq(
            Operatorname, Grp(F.Id("let")), Open,
            factorDefinition, SemiSpace,
            denominatorDefinition, SemiSpace,
            numeratorDefinition, SemiSpace,
            featureDefinition, SemiSpace,
            competitorDefinition, Close);

        Formula unitCirclePoleFree = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("w", complex)],
            Implies(
                Equal(Call("norm", w), D(1)),
                NotEqual(Call("eval", denominator, w), D(0))));
        Formula margin = Less(
            D(0),
            Call(
                "infDist",
                Apply(feature, Apply(point, D(0))),
                competitorSpace));
        Formula existsDepth = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("d"),
            natural,
            Seq(letObjects, Comma, Sp, And(unitCirclePoleFree, margin)));

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp,
                Typed(scaleCount, natural), Comma, Sp,
                Typed(competitorCount, natural), Comma),
            Seq(Typed(scale, Arrow(finScale, real)), Comma, Sp,
                Typed(scaleDepth, Arrow(finScale, natural)), Comma),
            Seq(Typed(F.Id("scaleInDisk"), scaleInDisk), Comma),
            Seq(Typed(point, Arrow(finPoint, complex)), Comma),
            Seq(Typed(F.Id("orbitDistinct"), orbitDistinct), Comma),
            Seq(Typed(F.Id("noPole"), noPole), Comma),
            Seq(existsDepth, Dot),
        ]));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(Open, binder, Sp, Mapsto, Sp, body, Close);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
}
