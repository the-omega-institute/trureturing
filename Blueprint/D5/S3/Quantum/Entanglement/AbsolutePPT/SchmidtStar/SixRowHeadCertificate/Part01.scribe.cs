using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate;
internal sealed class SixRowHeadCertificatePart01Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact homogeneous Bernstein certificates on the indicated closed subboxes of the K6 scalar domain. Each coefficient table is nonnegative by construction, and its identity is checked by ring normalization. These subbox results are consumed by the complete partition proof.", H("SixRowHeadCertificate/Part01"), Blocks(
            Paragraph(Text("Exact homogeneous Bernstein certificates on the indicated closed subboxes of the K6 scalar domain. Each coefficient table is nonnegative by construction, and its identity is checked by ring normalization. These subbox results are consumed by the complete partition proof.")),
            Describe.Lean(DescribeId.Create("sixrowhead-sixrowheadcertificate-part01-box0"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Part01.box0"),
                H("box0"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem box0 (z k h : ℝ) (hz : 0 ≤ z) (hZ : z ≤ (3/8)) (hk : 0 ≤ k) (hK : k ≤ 1) (hh : 0 ≤ h) (hH : h ≤ (3/2)) : 0 ≤ P z k h"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sixrowhead-sixrowheadcertificate-part01-box1"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Part01.box1"),
                H("box1"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem box1 (z k h : ℝ) (hz : (3/8) ≤ z) (hZ : z ≤ (9/16)) (hk : 0 ≤ k) (hK : k ≤ 1) (hh : 0 ≤ h) (hH : h ≤ (3/4)) : 0 ≤ P z k h"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sixrowhead-sixrowheadcertificate-part01-box2"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Part01.box2"),
                H("box2"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem box2 (z k h : ℝ) (hz : (9/16) ≤ z) (hZ : z ≤ (39/64)) (hk : 0 ≤ k) (hK : k ≤ (1/4)) (hh : 0 ≤ h) (hH : h ≤ (3/16)) : 0 ≤ P z k h"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sixrowhead-sixrowheadcertificate-part01-box3"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Part01.box3"),
                H("box3"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem box3 (z k h : ℝ) (hz : (39/64) ≤ z) (hZ : z ≤ (81/128)) (hk : 0 ≤ k) (hK : k ≤ (1/8)) (hh : 0 ≤ h) (hH : h ≤ (3/32)) : 0 ≤ P z k h"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sixrowhead-sixrowheadcertificate-part01-box4"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Part01.box4"),
                H("box4"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem box4 (z k h : ℝ) (hz : (39/64) ≤ z) (hZ : z ≤ (81/128)) (hk : 0 ≤ k) (hK : k ≤ (1/8)) (hh : (3/32) ≤ h) (hH : h ≤ (3/16)) : 0 ≤ P z k h"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sixrowhead-sixrowheadcertificate-part01-box5"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Part01.box5"),
                H("box5"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem box5 (z k h : ℝ) (hz : (39/64) ≤ z) (hZ : z ≤ (81/128)) (hk : (1/8) ≤ k) (hK : k ≤ (1/4)) (hh : 0 ≤ h) (hH : h ≤ (3/32)) : 0 ≤ P z k h"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sixrowhead-sixrowheadcertificate-part01-box6"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Part01.box6"),
                H("box6"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem box6 (z k h : ℝ) (hz : (39/64) ≤ z) (hZ : z ≤ (81/128)) (hk : (1/8) ≤ k) (hK : k ≤ (1/4)) (hh : (3/32) ≤ h) (hH : h ≤ (3/16)) : 0 ≤ P z k h"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sixrowhead-sixrowheadcertificate-part01-box7"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Part01.box7"),
                H("box7"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem box7 (z k h : ℝ) (hz : (9/16) ≤ z) (hZ : z ≤ (21/32)) (hk : 0 ≤ k) (hK : k ≤ (1/4)) (hh : (3/16) ≤ h) (hH : h ≤ (3/8)) : 0 ≤ P z k h"))), DescribeRole.Theorem)
        )));
}
