using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InstitutionalCapture;

internal sealed class ThresholdCollapseByCommonProvenanceDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal formal role counts can conceal radically different capture thresholds.",
        H("Threshold Collapse by Common Provenance"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("threshold-collapse-by-common-provenance"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/InstitutionalCapture/"
                        + "ThresholdCollapseByCommonProvenance."
                        + "threshold_collapse_by_common_provenance"),
                H("Common provenance collapses the capture threshold"),
                StatementSource.FromAuthor(ThresholdFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The formal roles are the n elements of Fin n, and both constructions use "
                            + "states in Fin n x Bool. The common-provenance readout ignores the "
                            + "state label, so every named role exposes the same Boolean source.")),
                    Paragraph(Text(
                        "The independent-provenance readout exposes the Boolean value only when "
                            + "the state's label matches the named source, returning false for all "
                            + "other labels. Consequently, each role has a distinct necessary "
                            + "source.")),
                    Paragraph(Text(
                        "For every positive n, the two systems therefore have the same formal role "
                            + "cardinality n while their exact capture numbers are one and n. "
                            + "Formal role multiplicity alone does not determine the capture "
                            + "threshold."))),
                DescribeRole.Theorem))));

    private static Formula Indexed(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula ThresholdFormula()
    {
        Formula n = F.Id("n");
        Formula finN = Call("Fin", n);
        Formula common = Indexed(F.Id("commonProvenanceReadout"), n);
        Formula independent = Indexed(F.Id("independentProvenanceReadout"), n);
        Formula commonCapture = Call("captureNumber", common, common);
        Formula independentCapture = Call("captureNumber", independent, independent);

        return Disp(Seq(
            Forall, Sp, n, Colon, Sp, F.Id("Nat"), Comma, Sp,
            D(0), Sp, Lt, Sp, n, Sp, Rightarrow, Esc,
            Call("card", finN), Sp, Eq, Sp, n, Sp, Land, Esc,
            commonCapture, Sp, Eq, Sp, D(1), Sp, Land, Esc,
            independentCapture, Sp, Eq, Sp, n, Dot));
    }
}
