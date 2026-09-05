using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class RationalWeilJetBudgetDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/ZetaBridge/RationalWeilJetBudget.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite rational expression bounds the actual mixed majorant and certifies the common depth and support radius, with analytic input premises explicit.",
        H("Rational Two-Jet Budget Verifier"),
        Blocks(
            Describe.Lean(DescribeId.Create("rational-weil-head-rationalSpectralHead"),
                DeclarationHandle.Create(Prefix + "rationalSpectralHead"),
                H("Finite spectral-head calculator"),
                StatementSource.FromAuthor(Disp(F.Id("Hbar=sum_(n in E) M_n/(1+lower_n^2)^2 in exact rational arithmetic."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("M bounds the analytic multiplicity and lower is a nonnegative lower enclosure of the absolute ordinate. The finite set E still refers to actual zero indices."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("rational-weil-head-fourthMomentSummand_le_rational_enclosure"),
                DeclarationHandle.Create(Prefix + "fourthMomentSummand_le_rational_enclosure"),
                H("One certified rational head bound"),
                StatementSource.FromAuthor(Disp(F.Id("For lower>=0, multiplicity_n<=M and lower<=|t_n|, m_n/(1+t_n^2)^2<=M/(1+lower^2)^2."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Compare positive denominators after squaring the nonnegative height bound, then use the multiplicity upper bound. The term carries full multiplicity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rational-weil-head-rationalSpectralHead_sound"),
                DeclarationHandle.Create(Prefix + "rationalSpectralHead_sound"),
                H("Finite head soundness"),
                StatementSource.FromAuthor(Disp(F.Id("Certified nonnegative lower ordinate bounds and multiplicity upper bounds on E imply sum_E fourthMomentSummand<=rationalSpectralHead(E,M,lower)."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Sum the pointwise inequalities and transport the rational arithmetic through the real embedding. No BPT half-endpoint convention is silently applied."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rationalweiljetbudget-rationalJetMajorant"),
                DeclarationHandle.Create(Prefix + "rationalJetMajorant"),
                H("Executable rational majorant"),
                StatementSource.FromAuthor(Disp(F.Id("Cbar=(sum_i 3*(J0_i+J2_i))^2*(H+Theta)."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All operations are finite rational sums, products and powers. The data acquire analytic meaning only through the soundness hypotheses."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("rationalweiljetbudget-rationalJetMajorant-sound"),
                DeclarationHandle.Create(Prefix + "rationalJetMajorant_sound"),
                H("Actual infinite family bound"),
                StatementSource.FromAuthor(Disp(F.Id("Unit-support tests, certified rational zeroth and second L1 seminorm enclosures, a finite spectral-head bound H, and a summable spectral tail bounded by Theta imply C_actual<=Cbar."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Derive both transform bounds by integration by parts. Apply the all-cross-term head-tail theorem and transfer the finite rational calculation to the reals. C_actual is a conclusion, not an input."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rationalweiljetbudget-rational-unit-packet-support-and-margin"),
                DeclarationHandle.Create(Prefix + "rational_unit_packet_support_and_margin"),
                H("Computed depth on the actual full Gram"),
                StatementSource.FromAuthor(Disp(F.Id("For a unit-support packet satisfying the stated two-jet and scalar spectral enclosures, and Cbar<=c/d, every N>=Nat.log4(floor(c*q/(d*p))) has support radius N+2 and full Gram bound Re(a*G_N a)<=-(4-p/q)E(a)."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The scalar spectral-tail estimate remains the independent number-theoretic obligation. No axiom for a published numerical estimate is added. Strict negativity additionally requires p/q<4 and a nonzero coefficient vector. The arithmetic examples are regression cases, not actual off-line zeta data."))), DescribeRole.Theorem)), []));
}
