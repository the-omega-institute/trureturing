using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Naming.Conservation;

internal sealed class GreenClassNamingConservationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform Green mass and countable-name conservation share one product carrier.",
        H("Green-Class Mass and Naming Conservation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("green-class-naming-conservation"),
                DeclarationHandle.Create(
                    "D5/S0/Naming/Conservation/GreenClassNamingConservation."
                    + "green_class_naming_conservation"),
                H("Finite certificates retain mass while countable names remain null"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let O be a finite nontrivial discrete measurable alphabet and equip the "
                        + "sequence space N -> O with the canonical uniform product probability "
                        + "measure stringMeasure O. A finite support S and target t determine the "
                        + "canonical greenClass S t.")),
                    Paragraph(Text(
                        "The green class has mass exactly (card O)^(-1) raised to card S and that "
                        + "mass is positive. Thus the value depends on the certificate budget and "
                        + "not on the pinned content.")),
                    Paragraph(Text(
                        "For every countably indexed family of canonical NamingSystem values, the "
                        + "union of named images is countable and null, while its complement has "
                        + "measure one. For every system and every height budget, the complement of "
                        + "the corresponding finite layer image also has measure one.")),
                    Paragraph(Text(
                        "The exact cylinder calculation and positivity are supplied by the frozen "
                        + "GreenClassMeasure declarations. The frozen NamingTowerConservation "
                        + "declaration supplies countability, nullity, and full-measure complement. "
                        + "Atomlessness of the same product measure follows from the imported "
                        + "critical-diameter estimate; probability normalization then also proves "
                        + "the sequence carrier uncountable."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Naming/GreenClassMeasure")),
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S0/Naming/Conservation/NamingTowerConservation"))
        ]));

    private static Formula Typeclass(string name, Formula argument) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, argument, Close, CloseBracket);

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula alphabet = F.Id("O");
        Formula stringType = Seq(naturals, Sp, To, Sp, alphabet);
        Formula support = F.Id("S"), target = F.Id("t");
        Formula indexType = F.Id("J"), systems = F.Id("systems");
        Formula index = F.Id("j"), budget = F.Id("Q");
        Formula name = F.Id("a"), point = F.Id("x");
        Formula systemAtIndex = Call("systems", index);
        Formula productMeasure = Call("stringMeasure", alphabet);
        Formula greenClass = Call("greenClass", support, target);
        Formula namedUnion = Call("iUnion", Seq(
            Lambda, Sp, index, Sp, Mapsto, Sp, Call("named", systemAtIndex)));
        Formula layerImage = new Formula.SetBuilder(
            Seq(
                Exists, Sp, name, Colon, Sp, Call("Name", systemAtIndex), Comma, Sp,
                name, Sp, InMacro, Sp, Call("layer", systemAtIndex, budget), Sp,
                Land, Sp,
                Call("assignment", systemAtIndex, name), Sp, Eq, Sp, Call("some", point)),
            point,
            stringType);
        Formula complement(Formula value) => Seq(value, Caret, Grp(F.Id("c")));
        Formula inverseCardinality = Call("inv", Call("card", alphabet));
        Formula exactMass = new Formula.Power(inverseCardinality, Call("card", support));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, alphabet, Colon, Sp, type, Comma, RowBreak, Grp(),
            Typeclass("Fintype", alphabet), Comma, Sp,
            Typeclass("Nonempty", alphabet), Comma, Sp,
            Typeclass("Nontrivial", alphabet), Comma, RowBreak, Grp(),
            Typeclass("MeasurableSpace", alphabet), Comma, Sp,
            Typeclass("MeasurableSingletonClass", alphabet), Comma, RowBreak, Grp(),
            Typeclass("TopologicalSpace", alphabet), Comma, Sp,
            Typeclass("DiscreteTopology", alphabet), Comma, RowBreak, Grp(),
            Forall, Sp, support, Colon, Sp, Call("Finset", naturals), Comma, Sp,
            target, Colon, Sp, stringType, Comma, RowBreak, Grp(),
            Mu, Colon, Eq, productMeasure, Comma, RowBreak, Grp(),
            Forall, Sp, indexType, Colon, Sp, type, Comma, Sp,
            Typeclass("Countable", indexType), Comma, RowBreak, Grp(),
            Forall, Sp, systems, Colon, Sp, indexType, Sp, To, Sp,
            Call("NamingSystem", stringType), Comma, RowBreak, Grp(),
            Mu, Open, greenClass, Close, Sp, Eq, Sp, exactMass,
            Sp, Land, Sp, RowBreak, Grp(),
            D(0), Sp, Lt, Sp, Mu, Open, greenClass, Close,
            Sp, Land, Sp, RowBreak, Grp(),
            Call("Countable", namedUnion),
            Sp, Land, Sp, RowBreak, Grp(),
            Mu, Open, namedUnion, Close, Sp, Eq, Sp, D(0),
            Sp, Land, Sp, RowBreak, Grp(),
            Mu, Open, complement(namedUnion), Close, Sp, Eq, Sp, D(1),
            Sp, Land, Sp, RowBreak, Grp(),
            Forall, Sp, index, Colon, Sp, indexType, Comma, Sp,
            budget, Colon, Sp, naturals, Comma, Sp,
            Mu, Open, complement(layerImage), Close, Sp, Eq, Sp, D(1), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
