using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar;
internal sealed class SixRowOuterScalarDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The scalar intervals follow the manuscript closed coverage. The n23 low interval retains the actual mass square, including the quartic and all q and r splits. At n24 the possible r=q=0 and W=4 corner has mass at least 144, above center 140. The imported middle theorem is used without reimplementing its certificate. These are scalar consequences, not a physical APPT extraction or concentration theorem.", H("SixRowOuterScalar"), Blocks(
            Paragraph(Text("The scalar intervals follow the manuscript closed coverage. The n23 low interval retains the actual mass square, including the quartic and all q and r splits. At n24 the possible r=q=0 and W=4 corner has mass at least 144, above center 140. The imported middle theorem is used without reimplementing its certificate. These are scalar consequences, not a physical APPT extraction or concentration theorem.")),
            Describe.Lean(DescribeId.Create("sixrowouter-sixrowouterscalar-head-cap-elimination"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterScalar.head_cap_elimination"),
                H("head cap elimination"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem head_cap_elimination (r H D a q d : ℝ) (h : PhysicalScalarHyp r H D a q) (hr : r ≤ 1/5) (hDd : D ≤ d) : Den r*W r H D a q ≤ Den r*(q+r*(6-15*r))+cn r*V r q ∧ Den r*W r H D a q ≤ Den r*(q+r*d)+An r*V r q"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sixrowouter-sixrowouterscalar-cap-interval-strict"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterScalar.cap_interval_strict"),
                H("cap interval strict"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem cap_interval_strict (r H D a q : ℝ) (h : PhysicalScalarHyp r H D a q) (hrl : 1/12 ≤ r) (hru : r ≤ 1/5) : W r H D a q < T138 r"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sixrowouter-sixrowouterscalar-low-w-le"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterScalar.low_W_le"),
                H("low W le"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem low_W_le (r H D a q : ℝ) (h : PhysicalScalarHyp r H D a q) (hr : r ≤ 1/12) : W r H D a q ≤ T144 r ∧ (W r H D a q=T144 r → r=0 ∧ q=0)"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sixrowouter-sixrowouterscalar-n24-low-strict"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterScalar.n24_low_strict"),
                H("n24 low strict"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem n24_low_strict (j r H D a q : ℝ) (h : PhysicalScalarHyp r H D a q) (hj : 15 ≤ j) (hr : r ≤ 1/12) : 0 < gap 144 j (1/140) r H D a q"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sixrowouter-sixrowouterscalar-continuous-strict"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterScalar.continuous_strict"),
                H("continuous strict"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem continuous_strict (r H D a q : ℝ) (h : PhysicalScalarHyp r H D a q) (hrl : 1/3 ≤ r) (hru : r ≤ 79/200) : W r H D a q < T138 r"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sixrowouter-sixrowouterscalar-variance-strict"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterScalar.variance_strict"),
                H("variance strict"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem variance_strict (r H D a q : ℝ) (h : PhysicalScalarHyp r H D a q) (hrl : 3/10 ≤ r) (hru : r ≤ 1/3) : W r H D a q < T138 r"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sixrowouter-sixrowouterscalar-base-strict"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterScalar.base_strict"),
                H("base strict"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem base_strict (r H D a q : ℝ) (h : PhysicalScalarHyp r H D a q) (hrl : 1/12 ≤ r) (hru : r ≤ 79/200) : W r H D a q < T138 r"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sixrowouter-sixrowouterscalar-n23-low-strict"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowOuterScalar.n23_low_strict"),
                H("n23 low strict"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem n23_low_strict (j r H D a q : ℝ) (h : PhysicalScalarHyp r H D a q) (hj : 15 ≤ j) (hr : r ≤ 1/12) : 0 < gap 138 j th23 r H D a q"))), DescribeRole.Theorem)
        )));
}
