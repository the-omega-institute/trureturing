using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Admissibility;

internal sealed class MurthyA077739CertificateHighDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Consumed decimal-block certificate rows for Murthy A077739, indices 500 through 999.",
        H("Murthy A077739 certificate rows 500 through 999"),
        Blocks(
            Describe.Lean(DescribeId.Create("murthy-a077739-certificate-high-entries"),
                DeclarationHandle.Create("D5/S1/Digit/Admissibility/MurthyA077739CertificateHigh.entries"),
                H("Ordered multiplier-count data"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Entry i is the list of multiplier-count pairs for n=500+i. "
                    + "A pair (j,c) prescribes c copies of the decimal block jn. "
                    + "The classification module concatenates the low and high arrays in index order "
                    + "to form its private certificateData. It checks the exact residual digit sum "
                    + "for every nonexceptional index below 1000 by kernel reduction, then uses "
                    + "the general certificate_sound and from_blocks proofs to obtain a witness. "
                    + "The literal rows alone prove neither admissibility nor nonexistence. "
                    + "These consumed data definitions supply no independent mathematical result "
                    + "or external problem resolution."))), DescribeRole.Definition))));
}
