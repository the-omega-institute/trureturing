using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Refinement;

internal sealed class InverseLimitDescentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compatible finite-stage maps induce a unique map on inverse-limit families, and surjective coordinates recover finite naturality.",
        H("Inverse-Limit Descent and Reverse Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("inverse-limit-descent-and-reverse"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Refinement/InverseLimitDescent."
                        + "inverse_limit_descent_and_reverse"),
                H("Inverse-limit maps descend uniquely and reflect finite naturality"),
                StatementSource.FromAuthor(DescentFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The source and target are inverse-stage systems with restriction channels "
                            + "satisfying identity and composition. A stage map is assumed to commute "
                            + "with every restriction channel.")),
                    Paragraph(Text(
                        "The induced map sends a compatible source family to the family obtained by "
                            + "applying the corresponding stage map at every coordinate. The public "
                            + "statement includes both its coordinate equation and uniqueness.")),
                    Paragraph(Text(
                        "Conversely, if every source coordinate is surjective from compatible "
                            + "families and a map with the displayed coordinate equation exists, "
                            + "evaluating compatibility on a lifted family recovers strict finite-stage "
                            + "naturality.")),
                    Paragraph(Text(
                        "The proof reuses the canonical InverseStageSystem and CompatibleStageFamily "
                            + "types from CompletionIsomorphismCriterion. Repository search found no "
                            + "existing theorem packaging this induced map with the reverse clause."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Stage(Formula family, Formula index) =>
        Seq(family, Underscore, Grp(index));

    private static Formula DescentFormula()
    {
        Formula indexType = F.Id("I");
        Formula source = F.Id("S");
        Formula target = F.Id("T");
        Formula delta = F.Id("Delta");
        Formula stageMap = F.Id("delta");
        Formula family = F.Id("a");
        Formula index = F.Id("i");
        Formula other = F.Id("j");
        Formula h = F.Id("h");
        Formula point = F.Id("x");
        Formula sourceFamilies = Call("CompatibleStageFamily", source);
        Formula targetFamilies = Call("CompatibleStageFamily", target);
        Formula coordinate = Seq(stageMap, Underscore, Grp(index));
        Formula equation = Seq(Stage(Apply(delta, family), index), Sp, Eq, Sp,
            Apply(coordinate, Stage(family, index)));
        Formula finiteNaturality = Seq(
            Call("restrict", target, h, Apply(Seq(stageMap, Underscore, Grp(other)), point)),
            Sp, Eq, Sp,
            Apply(coordinate, Call("restrict", source, h, point)));

        Formula existsUnique = Seq(
            Exists, Bang, Sp, F.Id("D"), Colon, Sp,
            sourceFamilies, Sp, Rightarrow, Sp, targetFamilies, Comma, Sp,
            Forall, Sp, family, Comma, Sp, index, Comma, Sp, equation);

        Formula reverse = Seq(
            Forall, Sp, F.Id("D"), Colon, Sp,
            sourceFamilies, Sp, Rightarrow, Sp, targetFamilies, Comma, Sp,
            Open, Forall, Sp, family, Comma, Sp, index, Comma, Sp, equation, Close,
            Sp, Rightarrow, Sp,
            Open, Forall, Sp, index, Comma, Sp,
            Call("Surjective", Seq(family, Underscore, Grp(index))), Close,
            Sp, Rightarrow, Sp,
            Forall, Sp, h, Comma, Sp, point, Comma, Sp, finiteNaturality);

        return Disp(Seq(
            Forall, Sp, indexType, Comma, Sp,
            source, Comma, Sp, target, Comma, Sp,
            stageMap, Comma, Sp, Call("Compatible", source, target, stageMap),
            Sp, Rightarrow, Sp, Open,
            existsUnique, Sp, Land, Sp, reverse, Close, Dot));
    }
}
