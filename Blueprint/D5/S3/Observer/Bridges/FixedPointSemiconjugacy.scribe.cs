using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Bridges;

internal sealed class FixedPointSemiconjugacyDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Bridges/FixedPointSemiconjugacy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A semiconjugate observer bridge transports fixed points and finite behavior.",
        H("Fixed-Point Transport Through Observer Bridges"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("semiconjugacy-transports-fixed-points"),
                DeclarationHandle.Create(Prefix + "fixed_point_maps"),
                H("Semiconjugacy transports fixed points"),
                StatementSource.FromAuthor(FixedPointFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let h semiconjugate a source update F to a target update G. "
                            + "Every fixed source state is sent to a fixed target state.")),
                    Paragraph(Text(
                        "The bridge preserves a typed dynamical relation. It does not identify "
                            + "the two state spaces, and reverse recovery requires injectivity.")),
                    Paragraph(Text(
                        "The same owner also proves forward invariance of observation fibers and "
                            + "transport of every finite iterate."))),
                DescribeRole.Theorem))));

    private static Formula FixedPointFormula()
    {
        Formula h = F.Id("h");
        Formula source = F.Id("F");
        Formula target = F.Id("G");
        Formula x = F.Id("x");
        return Disp(Seq(
            Call("Semiconj", h, source, target), Sp, Land, Sp,
            Call("IsFixedPt", source, x), Sp, Rightarrow, Sp,
            Call("IsFixedPt", target, Call("h", x))));
    }
}
