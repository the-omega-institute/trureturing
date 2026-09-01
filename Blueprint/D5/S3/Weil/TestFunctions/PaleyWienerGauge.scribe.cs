using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.TestFunctions;

internal sealed class PaleyWienerGaugeDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Weil/TestFunctions/PaleyWienerGauge.paleyWienerGauge";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equality of tempered distributions on tests supported in an open window defines "
            + "the Paley-Wiener gauge equivalence relation.",
        H("Paley-Wiener L-Gauge"),
        Blocks(Describe.Lean(
            DescribeId.Create("paley-wiener-l-gauge"),
            DeclarationHandle.Create(Declaration),
            H("Paley-Wiener gauge on tempered distributions"),
            StatementSource.FromAuthor(GaugeFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The restriction of a tempered distribution is represented by all of "
                        + "its values on Schwartz tests whose topological support lies in "
                        + "the open interval (-2L, 2L). The gauge is the Setoid kernel of "
                        + "this restriction map, so reflexivity, symmetry, and transitivity "
                        + "are inherited from equality.")),
                Paragraph(Text(
                    "The Lean module also proves that the relation is genuinely coarser "
                        + "than equality: the zero distribution and the Dirac distribution "
                        + "at the excluded endpoint 2L have the same window restriction but "
                        + "are distinct."))),
            DescribeRole.Definition))));

    private static Formula GaugeFormula()
    {
        Formula real = Call("Real"), complex = Call("Complex");
        Formula scale = F.Id("L");
        Formula left = F.Id("W1"), right = F.Id("W2"), test = F.Id("phi");
        Formula distribution = Call("TemperedDistribution", real, complex);
        Formula schwartz = Call("SchwartzMap", real, complex);
        Formula doubledScale = new Formula.Binary(
            D(2), FormulaBinaryOperator.Multiply, scale);
        Formula window = Call("Ioo", new Formula.Negate(doubledScale), doubledScale);
        Formula supportCondition = Seq(
            Call("tsupport", test), Sp, Subseteq, Sp, window);
        Formula actionEquality = Seq(
            new Formula.Apply(left, [test]), Sp, Eq, Sp,
            new Formula.Apply(right, [test]));
        Formula relation = Call("PaleyWienerGauge", scale, left, right);

        return Disp(Seq(
            Forall, Sp, scale, Colon, Sp, real, Comma, Sp,
            left, Comma, Sp, right, Colon, Sp, distribution, Comma, RowBreak, Grp(),
            relation, Sp, Leftrightarrow, Sp,
            Forall, Sp, test, Colon, Sp, schwartz, Comma, Sp,
            supportCondition, Sp, Rightarrow, Sp, actionEquality, Dot));
    }
}
