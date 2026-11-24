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
                            + "after the readout transport. A source point witnessing image "
                            + "membership supplies the four pointwise equations used in the proof."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula FunctionType(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Pointwise(Formula point, Formula left, Formula right) =>
        Seq(Open, Forall, Sp, point, Comma, Sp, left, Sp, Eq, Sp, right, Close);

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
        Formula transport = Pointwise(point,
            Apply(tPrime, Apply(sourceMap, point)), Apply(targetMap, Apply(t, point)));
        Formula readoutNaturality = Pointwise(point,
            Apply(cPrime, Apply(sourceMap, point)), Apply(readoutMap, Apply(c, point)));
        Formula factorization = Pointwise(point, Apply(t, point), Apply(factor, Apply(c, point)));
        Formula factorizationPrime = Pointwise(point,
            Apply(tPrime, point), Apply(factorPrime, Apply(cPrime, point)));
        Formula inRange = Seq(
            value, Sp, InMacro, Sp, Apply(range, c));
        Formula conclusion = Seq(
            Apply(targetMap, Apply(factor, value)), Sp, Eq, Sp,
            Apply(factorPrime, Apply(readoutMap, value)));
        Formula maps = Seq(
            c, Colon, Sp, FunctionType(source, readout), Comma, Sp,
            cPrime, Colon, Sp, FunctionType(sourcePrime, readoutPrime), Comma, Sp,
            t, Colon, Sp, FunctionType(source, target), Comma, Sp,
            tPrime, Colon, Sp, FunctionType(sourcePrime, targetPrime), Comma, Sp,
            factor, Colon, Sp, FunctionType(readout, target), Comma, Sp,
            factorPrime, Colon, Sp, FunctionType(readoutPrime, targetPrime), Comma, Sp,
            sourceMap, Colon, Sp, FunctionType(source, sourcePrime), Comma, Sp,
            readoutMap, Colon, Sp, FunctionType(readout, readoutPrime), Comma, Sp,
            targetMap, Colon, Sp, FunctionType(target, targetPrime));
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
            Forall, Sp, value, Colon, Sp, readout, Comma, Sp,
            inRange, Sp, Rightarrow, Sp, conclusion, Dot));
    }
}
