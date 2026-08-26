using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Transportability;

internal sealed class EffectiveImageNaturalitySurjectiveLiftDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Transportability/EffectiveImageNaturalitySurjectiveLift."
            + "effective_image_naturality_and_surjective_lift";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Transport factorization is natural on the effective image and globally for a surjective readout.",
        H("Effective-Image Naturality and Surjective Lift"),
        Blocks(Describe.Lean(
            DescribeId.Create("effective-image-naturality-and-surjective-lift"),
            DeclarationHandle.Create(Declaration),
            H("Image-local naturality extends across a surjective readout"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The transport square, readout square, and both target factorizations "
                        + "are public premises on their exact carriers.")),
                Paragraph(Text(
                    "The first conclusion states naturality on the range of the current "
                        + "readout. The second independently assumes that readout is "
                        + "surjective and states the equation on its full codomain.")),
                Paragraph(Text(
                    "The image-local clause is imported from the frozen family theorem; "
                        + "surjectivity supplies a source representative for the global clause."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula At(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Compose(Formula left, Formula right) =>
        Seq(left, Sp, Circ, Sp, right);

    private static Formula Concept(Formula domain, Formula codomain) =>
        Call("Concept", domain, codomain);

    private static Formula TheoremFormula()
    {
        Formula source = F.Id("XE");
        Formula sourcePrime = F.Id("XEPrime");
        Formula readout = F.Id("YE");
        Formula readoutPrime = F.Id("YEPrime");
        Formula target = F.Id("WE");
        Formula targetPrime = F.Id("WEPrime");
        Formula c = F.Id("C");
        Formula cPrime = F.Id("CPrime");
        Formula t = F.Id("T");
        Formula tPrime = F.Id("TPrime");
        Formula factor = F.Id("f");
        Formula factorPrime = F.Id("fPrime");
        Formula sourceMap = F.Id("Xmap");
        Formula readoutMap = F.Id("Bmap");
        Formula targetMap = F.Id("Ymap");
        Formula value = F.Id("y");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula equation = Seq(
            At(targetMap, At(factor, value)), Sp, Eq, Sp,
            At(factorPrime, At(readoutMap, value)));
        Formula imageClause = Seq(
            Forall, Sp, value, Colon, Sp, readout, Comma, Sp,
            value, Sp, InMacro, Sp, Call("range", c), Sp, Rightarrow, Sp, equation);
        Formula globalClause = Seq(
            Call("Surjective", c), Sp, Rightarrow, Sp,
            Open, Forall, Sp, value, Colon, Sp, readout, Comma, Sp, equation, Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, source, Comma, Sp, sourcePrime, Comma, Sp,
            readout, Comma, Sp, readoutPrime, Comma, Sp,
            target, Comma, Sp, targetPrime, Colon, Sp, type, Comma, RowBreak, Grp(),
            c, Colon, Sp, Concept(source, readout), Comma, Sp,
            cPrime, Colon, Sp, Concept(sourcePrime, readoutPrime), Comma, RowBreak, Grp(),
            t, Colon, Sp, Concept(source, target), Comma, Sp,
            tPrime, Colon, Sp, Concept(sourcePrime, targetPrime), Comma, RowBreak, Grp(),
            factor, Colon, Sp, Concept(readout, target), Comma, Sp,
            factorPrime, Colon, Sp, Concept(readoutPrime, targetPrime), Comma,
            RowBreak, Grp(),
            sourceMap, Colon, Sp, Concept(source, sourcePrime), Comma, Sp,
            readoutMap, Colon, Sp, Concept(readout, readoutPrime), Comma, Sp,
            targetMap, Colon, Sp, Concept(target, targetPrime), Comma, RowBreak, Grp(),
            Compose(tPrime, sourceMap), Sp, Eq, Sp, Compose(targetMap, t), Sp,
            Land, RowBreak, Grp(),
            Compose(cPrime, sourceMap), Sp, Eq, Sp, Compose(readoutMap, c), Sp,
            Land, RowBreak, Grp(),
            t, Sp, Eq, Sp, Compose(factor, c), Sp, Land, RowBreak, Grp(),
            tPrime, Sp, Eq, Sp, Compose(factorPrime, cPrime), Sp,
            Rightarrow, RowBreak, Grp(),
            Open, imageClause, Close, Sp, Land, RowBreak, Grp(),
            Open, globalClause, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
