using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadCertificate;
internal sealed class SixRowHeadCertificatePart02Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact homogeneous Bernstein certificates on the indicated closed subboxes of the K6 scalar domain. Each coefficient table is nonnegative by construction, and its identity is checked by ring normalization. These subbox results are consumed by the complete partition proof.", H("SixRowHeadCertificate/Part02"), Blocks(
            Paragraph(Text("Exact homogeneous Bernstein certificates on the indicated closed subboxes of the K6 scalar domain. Each coefficient table is nonnegative by construction, and its identity is checked by ring normalization. These subbox results are consumed by the complete partition proof.")),
            Describe.Lean(DescribeId.Create("sixrowhead-sixrowheadcertificate-part02-box8"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Part02.box8"),
                H("box8"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem box8 (z k h : ℝ) (hz : (9/16) ≤ z) (hZ : z ≤ (39/64)) (hk : (1/4) ≤ k) (hK : k ≤ (1/2)) (hh : 0 ≤ h) (hH : h ≤ (3/16)) : 0 ≤ P z k h"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sixrowhead-sixrowheadcertificate-part02-box9"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Part02.box9"),
                H("box9"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem box9 (z k h : ℝ) (hz : (39/64) ≤ z) (hZ : z ≤ (81/128)) (hk : (1/4) ≤ k) (hK : k ≤ (3/8)) (hh : 0 ≤ h) (hH : h ≤ (3/32)) : 0 ≤ P z k h"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sixrowhead-sixrowheadcertificate-part02-box10"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Part02.box10"),
                H("box10"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem box10 (z k h : ℝ) (hz : (39/64) ≤ z) (hZ : z ≤ (81/128)) (hk : (1/4) ≤ k) (hK : k ≤ (3/8)) (hh : (3/32) ≤ h) (hH : h ≤ (3/16)) : 0 ≤ P z k h"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sixrowhead-sixrowheadcertificate-part02-box11"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Part02.box11"),
                H("box11"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem box11 (z k h : ℝ) (hz : (39/64) ≤ z) (hZ : z ≤ (81/128)) (hk : (3/8) ≤ k) (hK : k ≤ (1/2)) (hh : 0 ≤ h) (hH : h ≤ (3/32)) : 0 ≤ P z k h"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sixrowhead-sixrowheadcertificate-part02-box12"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Part02.box12"),
                H("box12"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem box12 (z k h : ℝ) (hz : (39/64) ≤ z) (hZ : z ≤ (81/128)) (hk : (3/8) ≤ k) (hK : k ≤ (1/2)) (hh : (3/32) ≤ h) (hH : h ≤ (3/16)) : 0 ≤ P z k h"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sixrowhead-sixrowheadcertificate-part02-box13"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Part02.box13"),
                H("box13"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem box13 (z k h : ℝ) (hz : (9/16) ≤ z) (hZ : z ≤ (39/64)) (hk : (1/4) ≤ k) (hK : k ≤ (1/2)) (hh : (3/16) ≤ h) (hH : h ≤ (3/8)) : 0 ≤ P z k h"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sixrowhead-sixrowheadcertificate-part02-box14"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Part02.box14"),
                H("box14"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem box14 (z k h : ℝ) (hz : (39/64) ≤ z) (hZ : z ≤ (81/128)) (hk : (1/4) ≤ k) (hK : k ≤ (3/8)) (hh : (3/16) ≤ h) (hH : h ≤ (9/32)) : 0 ≤ P z k h"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sixrowhead-sixrowheadcertificate-part02-box15"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate/Part02.box15"),
                H("box15"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem box15 (z k h : ℝ) (hz : (39/64) ≤ z) (hZ : z ≤ (21/32)) (hk : (1/4) ≤ k) (hK : k ≤ (3/8)) (hh : (9/32) ≤ h) (hH : h ≤ (3/8)) : 0 ≤ P z k h"))), DescribeRole.Theorem)
        )));
}
