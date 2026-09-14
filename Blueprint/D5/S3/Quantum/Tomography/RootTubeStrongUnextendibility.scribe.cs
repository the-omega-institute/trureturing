using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography;

internal sealed class RootTubeStrongUnextendibilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A complete residual-tube cover and an empty common-partner certificate exclude even one additional unbiased vector.",
        H("Strong Unextendibility from Refined Root Tubes"),
        Blocks(Describe.Lean(
            DescribeId.Create("six-frame-has-cross-error-to-any-covered-point"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/Tomography/RootTubeStrongUnextendibility."
                + "six_frame_has_cross_error_to_any_covered_point"),
            H("Every covered additional point has a quantitative cross error"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Take matrix-valued tubes indexed by kappa. Same-tube real trace overlaps are at least mu, "
                    + "within-frame overlaps are below eta, and eta is at most mu. The orthogonality and "
                    + "unbiasedness relations are one-sided enclosures of the actual trace conditions. "
                    + "For every injective orthogonality six-clique, no label is unbiased to all six labels. "
                    + "If every member of a six-frame C and an additional point Q lies in the complete cover, "
                    + "then some real trace overlap Tr(C_i Q) differs from 1/6 by at least tau.")),
                Paragraph(Text(
                    "The same-tube lower bound forces the six labels to be distinct. Their small internal "
                    + "overlaps place them in the orthogonality candidate relation. The empty-partner "
                    + "certificate supplies one forbidden cross pair for the label of Q. The unbiased "
                    + "enclosure then gives the stated error. This reuses the existing matrix and tube "
                    + "interfaces; it does not introduce a second definition of MUBs or of a projector.")),
                Paragraph(Text(
                    "The concrete research instance refines one residual tube and checks every first "
                    + "six-clique. Empty, overlapping and multiple-root tubes are permitted. The actual "
                    + "residual-sublevel cover, soundness of the refinement, and finite relation certificate "
                    + "must still be supplied as mathematical proofs. External checker output does not "
                    + "discharge these Lean hypotheses. The authoring run did not execute Lean or Scribe."))),
            DescribeRole.Theorem))));

    private static Formula Apply(string name, params Formula[] arguments)
    {
        var parts = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) { parts.Add(Comma); parts.Add(Sp); }
            parts.Add(arguments[i]);
        }
        parts.Add(Close);
        return Seq([.. parts]);
    }

    private static Formula TheoremFormula() => Disp(Seq(
        Apply("CompleteTubeAndOverlapBounds", F.Id("T"), F.Id("C"), F.Id("Q")),
        Sp, Land, Sp, Apply("NoCommonPartnerOfAnySixClique", F.Id("O"), F.Id("B")),
        Sp, Rightarrow, RowBreak,
        Apply("ExistsCrossErrorAtLeast", F.Id("C"), F.Id("Q"), F.Id("tau")), Dot));
}
