using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Transport;

internal sealed class EffectiveImageNaturalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Transport factorization is natural on the effective image.",
        H("Effective-Image Naturality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("effective-image-naturality"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Transport/EffectiveImageNaturality."
                        + "effective_image_naturality"),
                H("Naturality on the effective image"),
                StatementSource.FromAuthor(Formula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The source and target carriers are explicit concept readouts. "
                            + "The transport equation and the readout equation are both public, "
                            + "as are the two factorization equations for the current and "
                            + "transported maps.")),
                    Paragraph(Text(
                        "For every value in the range of the first readout, transporting "
                            + "after applying its factor equals applying the transported factor "
                            + "after the readout transport. The proof evaluates the four public "
                            + "equations at a source point and uses equality congruence.")),
                    Paragraph(Text(
                        "The canonical Concept carrier is imported from the existing family. "
                            + "Repository and pinned-library searches found no exact theorem "
                            + "packaging these two naturality clauses with the effective-image "
                            + "conclusion."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Compose(Formula left, Formula right) =>
        Seq(left, Sp, Circ, Sp, right);

    private static Formula Concept(Formula domain, Formula codomain) =>
        Seq(Operatorname, Grp(F.Id("Concept")), Open, domain, Comma, Sp, codomain, Close);

    private static Formula Formula()
    {
        Formula source = F.Id("X");
        Formula sourcePrime = F.Id("Xprime");
        Formula readout = F.Id("Y");
        Formula readoutPrime = F.Id("Yprime");
        Formula target = F.Id("W");
        Formula targetPrime = F.Id("Wprime");
        Formula c = F.Id("C");
        Formula cPrime = F.Id("Cprime");
        Formula t = F.Id("T");
        Formula tPrime = F.Id("Tprime");
        Formula factor = F.Id("f");
        Formula factorPrime = F.Id("fprime");
        Formula sourceMap = F.Id("Xmap");
        Formula readoutMap = F.Id("Bmap");
        Formula targetMap = F.Id("Ymap");
        Formula value = F.Id("y");
        Formula point = F.Id("x");
        Formula range = Seq(Operatorname, Grp(F.Id("range")));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula transport = Seq(
            Compose(tPrime, sourceMap), Sp, Eq, Sp, Compose(targetMap, t));
        Formula readoutNaturality = Seq(
            Compose(cPrime, sourceMap), Sp, Eq, Sp, Compose(readoutMap, c));
        Formula factorization = Seq(
            t, Sp, Eq, Sp, Compose(factor, c));
        Formula factorizationPrime = Seq(
            tPrime, Sp, Eq, Sp, Compose(factorPrime, cPrime));
        Formula inRange = Seq(
            value, Sp, InMacro, Sp, Apply(range, c));
        Formula conclusion = Seq(
            Apply(targetMap, Apply(factor, value)), Sp, Eq, Sp,
            Apply(factorPrime, Apply(readoutMap, value)));
        Formula maps = Seq(
            c, Colon, Sp, Concept(source, readout), Comma, Sp,
            cPrime, Colon, Sp, Concept(sourcePrime, readoutPrime), Comma, Sp,
            t, Colon, Sp, Concept(source, target), Comma, Sp,
            tPrime, Colon, Sp, Concept(sourcePrime, targetPrime), Comma, Sp,
            factor, Colon, Sp, Concept(readout, target), Comma, Sp,
            factorPrime, Colon, Sp, Concept(readoutPrime, targetPrime), Comma, Sp,
            sourceMap, Colon, Sp, Concept(source, sourcePrime), Comma, Sp,
            readoutMap, Colon, Sp, Concept(readout, readoutPrime), Comma, Sp,
            targetMap, Colon, Sp, Concept(target, targetPrime));
        Formula types = Seq(
            source, Comma, Sp, sourcePrime, Comma, Sp, readout, Comma, Sp,
            readoutPrime, Comma, Sp, target, Comma, Sp, targetPrime,
            Colon, Sp, type);

        return Disp(Seq(
            Forall, Sp, types, Comma, Esc,
            maps, Comma, Esc,
            transport, Sp, Land, Sp,
            readoutNaturality, Sp, Land, Sp,
            factorization, Sp, Land, Sp,
            factorizationPrime, Sp, Rightarrow, Esc,
            Forall, Sp, value, Colon, Sp, target, Comma, Sp,
            inRange, Sp, Rightarrow, Sp, conclusion, Dot));
    }
}
