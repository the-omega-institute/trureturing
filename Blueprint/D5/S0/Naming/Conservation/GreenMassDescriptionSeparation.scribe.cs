using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Naming.Conservation;

internal sealed class GreenMassDescriptionSeparationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Green mass and description cost vary independently on one binary table carrier.",
        H("Green Mass and Description-Cost Separation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("green-mass-description-separation"),
                DeclarationHandle.Create(
                    "D5/S0/Naming/Conservation/GreenMassDescriptionSeparation."
                    + "green_mass_naming_conservation_and_description_separation"),
                H("Equal Green mass permits distinct description costs"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix a binary description machine with compiler overhead c. On the same "
                        + "binary sequence carrier, a finite support and target retain the exact "
                        + "Green-class mass while every countable naming family and every finite "
                        + "height layer leave a full-measure anonymous complement.")),
                    Paragraph(Text(
                        "At every length l, the all-zero table has Green mass exactly 2^(-l) and "
                        + "description complexity at most 2 log_2(l+1)+c. Thus arbitrarily deep "
                        + "finite certificates can remain succinctly described while their "
                        + "residual mass follows the independent budget exponent.")),
                    Paragraph(Text(
                        "Whenever the logarithmic zero-code bound is below l, an incompressible "
                        + "mask has strictly greater description complexity. Extending that mask "
                        + "to a binary sequence gives a Green class with exactly the same mass as "
                        + "the zero table at the same support budget.")),
                    Paragraph(Text(
                        "The proof directly applies the frozen conservation and incompressible-XOR "
                        + "owners. The new conclusion couples their public outputs on one carrier; "
                        + "it neither replaces the Green class nor assumes the desired separation."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S0/Naming/Conservation/GreenClassNamingConservation")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S0/Computability/DescriptionComplexity/XorTransformationTightness"))
        ]));

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula Lambda(Formula binder, Formula domain, Formula body) =>
        Seq(Open, binder, Colon, Sp, domain, Sp, Mapsto, Sp, body, Close);

    private static Formula Typeclass(string name, Formula argument) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, argument, Close, CloseBracket);

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula binary = Call("Fin", D(2));
        Formula sequences = Seq(naturals, Sp, To, Sp, binary);
        Formula overhead = F.Id("c");
        Formula machine = F.Id("M");
        Formula support = F.Id("S");
        Formula target = F.Id("t");
        Formula indexType = F.Id("J");
        Formula systems = F.Id("systems");
        Formula index = F.Id("j");
        Formula budget = F.Id("Q");
        Formula name = F.Id("a");
        Formula point = F.Id("x");
        Formula length = F.Id("l");
        Formula mask = F.Id("r");
        Formula maskTarget = F.Id("u");
        Formula coordinate = F.Id("i");
        Formula productMeasure = Call("stringMeasure", binary);
        Formula systemAtIndex = Call("systems", index);
        Formula namedUnion = Call("iUnion", Lambda(
            index, indexType, Call("named", systemAtIndex)));
        Formula layerImage = new Formula.SetBuilder(
            Seq(
                Exists, Sp, name, Colon, Sp, Call("Name", systemAtIndex), Comma, Sp,
                name, Sp, InMacro, Sp, Call("layer", systemAtIndex, budget), Sp,
                Land, Sp,
                Call("assignment", systemAtIndex, name), Sp, Eq, Sp, Call("some", point)),
            point,
            sequences);
        Formula complement(Formula value) => Seq(value, Caret, Grp(F.Id("c")));
        Formula inverseCardinality = Call("inv", Call("card", binary));
        Formula supportMass = new Formula.Power(inverseCardinality, Call("card", support));
        Formula lengthMass = Call("pow", inverseCardinality, length);
        Formula zeroSequence = Lambda(F.Id("k"), naturals, D(0));
        Formula zeroTable = Call("zero", Arrow(Call("Fin", length), binary));
        Formula objectSystem = Call("objects", machine, length);
        Formula complexity(Formula value) =>
            Call("descriptionComplexity", objectSystem, value);
        Formula logBound = Seq(
            D(2), Sp, Times, Sp, Call("natLog", D(2), Seq(length, Sp, Plus, Sp, D(1))),
            Sp, Plus, Sp, overhead);
        Formula range = Call("range", length);
        Formula zeroGreen = Call("greenClass", range, zeroSequence);

        Formula conservation = Seq(
            Forall, Sp, indexType, Colon, Sp, type, Comma, Sp,
            Typeclass("Countable", indexType), Comma, RowBreak, Grp(),
            Forall, Sp, systems, Colon, Sp, indexType, Sp, To, Sp,
            Call("NamingSystem", sequences), Comma, RowBreak, Grp(),
            Mu, Open, Call("greenClass", support, target), Close,
            Sp, Eq, Sp, supportMass, Sp, Land, Sp, RowBreak, Grp(),
            D(0), Sp, Lt, Sp, Mu, Open, Call("greenClass", support, target), Close,
            Sp, Land, Sp, RowBreak, Grp(),
            Call("Countable", namedUnion), Sp, Land, Sp, RowBreak, Grp(),
            Mu, Open, namedUnion, Close, Sp, Eq, Sp, D(0),
            Sp, Land, Sp, RowBreak, Grp(),
            Mu, Open, complement(namedUnion), Close, Sp, Eq, Sp, D(1),
            Sp, Land, Sp, RowBreak, Grp(),
            Forall, Sp, index, Colon, Sp, indexType, Comma, Sp,
            budget, Colon, Sp, naturals, Comma, Sp,
            Mu, Open, complement(layerImage), Close, Sp, Eq, Sp, D(1));

        Formula compressibleFamily = Seq(
            Forall, Sp, length, Colon, Sp, naturals, Comma, Sp,
            Mu, Open, zeroGreen, Close, Sp, Eq, Sp, lengthMass,
            Sp, Land, Sp, RowBreak, Grp(),
            complexity(zeroTable), Sp, Leq, Sp, logBound);

        Formula agreement = Seq(
            Forall, Sp, coordinate, Colon, Sp, Call("Fin", length), Comma, Sp,
            Call("u", coordinate), Sp, Eq, Sp, Call("r", coordinate));
        Formula equalMassSeparation = Seq(
            Forall, Sp, length, Colon, Sp, naturals, Comma, Sp,
            logBound, Sp, Lt, Sp, length, Sp, Implies, Sp, RowBreak, Grp(),
            Exists, Sp, mask, Colon, Sp, Arrow(Call("Fin", length), binary), Comma, Sp,
            maskTarget, Colon, Sp, sequences, Comma, RowBreak, Grp(),
            Open, agreement, Close, Sp, Land, Sp, RowBreak, Grp(),
            complexity(zeroTable), Sp, Lt, Sp, complexity(mask),
            Sp, Land, Sp, RowBreak, Grp(),
            Mu, Open, Call("greenClass", range, maskTarget), Close,
            Sp, Eq, Sp, lengthMass, Sp, Land, Sp, RowBreak, Grp(),
            Mu, Open, zeroGreen, Close, Sp, Eq, Sp, lengthMass);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, overhead, Colon, Sp, naturals, Comma, Sp,
            machine, Colon, Sp, Call("BinaryDescriptionMachine", overhead), Comma,
            RowBreak, Grp(),
            Forall, Sp, support, Colon, Sp, Call("Finset", naturals), Comma, Sp,
            target, Colon, Sp, sequences, Comma, RowBreak, Grp(),
            Mu, Colon, Eq, productMeasure, Comma, RowBreak, Grp(),
            Open, conservation, Close, Sp, Land, Sp, RowBreak, Grp(),
            Open, compressibleFamily, Close, Sp, Land, Sp, RowBreak, Grp(),
            Open, equalMassSeparation, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
