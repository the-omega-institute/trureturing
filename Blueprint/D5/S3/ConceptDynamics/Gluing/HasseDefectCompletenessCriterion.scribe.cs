using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Gluing;

internal sealed class HasseDefectCompletenessCriterionDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Gluing/HasseDefectCompletenessCriterion."
            + "hasse_complete_iff_positive_negative_defects_empty";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A local predicate family is Hasse complete exactly when both directional defect "
            + "sets are empty.",
        H("Hasse Completeness and Directional Defects"),
        Blocks(Describe.Lean(
            DescribeId.Create("hasse-completeness-is-two-sided-defect-emptiness"),
            DeclarationHandle.Create(Declaration),
            H("Hasse completeness is equivalent to two empty defect sets"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The positive defect set contains objects satisfying every local "
                        + "predicate but not the global predicate. The negative defect set "
                        + "contains globally valid objects rejected by at least one local "
                        + "predicate.")),
                Paragraph(Text(
                    "Pointwise global-local equivalence excludes both sets. Conversely, "
                        + "their separate emptiness supplies the two implications of the "
                        + "equivalence for every object."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula carrier = F.Id("X");
        Formula indexType = F.Id("I");
        Formula global = F.Id("P");
        Formula local = F.Id("L");
        Formula element = F.Id("x");
        Formula index = F.Id("i");
        Formula prop = Seq(Operatorname, Grp(F.Id("Prop")));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula globalAtElement = Apply(global, element);
        Formula allLocal = Seq(
            Forall, Sp, index, Colon, Sp, indexType, Comma, Sp,
            Apply(Apply(local, index), element));
        Formula positiveDefect = Seq(
            OpenBrace, element, Colon, Sp, carrier, Sp, Mid, Sp,
            Open, allLocal, Close, Sp, Land, Sp, Neg, Sp, globalAtElement,
            CloseBrace);
        Formula negativeDefect = Seq(
            OpenBrace, element, Colon, Sp, carrier, Sp, Mid, Sp,
            globalAtElement, Sp, Land, Sp, Neg, Open, allLocal, Close,
            CloseBrace);
        Formula completeness = Seq(
            Forall, Sp, element, Colon, Sp, carrier, Comma, Sp,
            globalAtElement, Sp, Iff, Sp, Open, allLocal, Close);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, carrier, Comma, Sp, indexType, Colon, Sp, type,
                Comma, Sp, global, Colon, Sp, carrier, Sp, To, Sp, prop,
                Comma),
            Seq(
                local, Colon, Sp, indexType, Sp, To, Sp, carrier, Sp, To, Sp,
                prop, Comma),
            Seq(Open, completeness, Close, Sp, Iff),
            Seq(
                positiveDefect, Sp, Eq, Sp, Emptyset, Sp, Land),
            Seq(negativeDefect, Sp, Eq, Sp, Emptyset, Dot),
        ]));
    }

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);
}
