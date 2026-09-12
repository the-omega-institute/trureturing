using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenPrimeCircle;

internal sealed class GoldenClockResolutionCoverDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/GoldenPrimeCircle/GoldenClockResolutionCover.";

    public DocumentDefinition Create() => DocumentDefinition.Create(
        ScribeNode.Create(
            "The golden event cover is uniform over nonnegative time and all resolutions. "
                + "The full integer extension has an explicitly located negative seam.",
            H("Golden Clock Resolution Cover"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("golden-clock-seam"),
                    DeclarationHandle.Create(Prefix + "seam_forces_negative_time"),
                    H("The intermediate cut has one possible integer location"),
                    StatementSource.FromAuthor(SeamFormula()),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "If phaseCoordinate(L,e,h)=alpha^2, irrationality forces "
                                + "e=-F(L+4). The companion negative_one_entry theorem "
                                + "identifies this same integer as entry(L,-1). "
                                + "Thus an open-arc split cannot silently be promoted "
                                + "from natural time to all integer time."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("golden-clock-resolution-cover"),
                    DeclarationHandle.Create(Prefix + "resolution_cover_nonnegative"),
                    H("Every nonnegative event belongs to one of two finer descriptions"),
                    StatementSource.FromAuthor(CoverFormula()),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For every natural L and every integer e>=0, Hits(L,e) "
                                + "is equivalent to Hits(L+2,e) or "
                                + "Hits(L+1,e+F(L+2)). The proof splits the normalized "
                                + "phase at alpha^2 and explicitly excludes the seam.")),
                        Paragraph(Text(
                            "The Lean declaration asserts exact coverage. A claim of "
                                + "disjointness, an identification with actual digit "
                                + "successors, or a finite-frequency estimate requires "
                                + "its corresponding additional theorem."))),
                    DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) { items.Add(Comma); items.Add(Sp); }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula SeamFormula() => Disp(Seq(
        F.Id("e"), Sp, Eq, Sp,
        Call("neg", Call("leading", Seq(F.Id("L"), Plus, F.Id("1"))))));

    private static Formula CoverFormula() => Disp(Call("equivalent",
        Call("Hits", F.Id("L"), F.Id("e")),
        Call("or",
            Call("Hits", Seq(F.Id("L"), Plus, F.Id("2")), F.Id("e")),
            Call("Hits", Seq(F.Id("L"), Plus, F.Id("1")),
                Seq(F.Id("e"), Plus, Call("boundary", F.Id("L")))))));
}
