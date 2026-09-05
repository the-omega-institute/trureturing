using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class WeilMixedHeadTailBudgetDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/ZetaBridge/WeilMixedHeadTailBudget.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite transform enclosures and a scalar fourth-moment tail control the actual full mixed-majorant constant without assuming a bound on that operator-family constant.",
        H("Finite Head and Fourth-Moment Tail Budget"),
        Blocks(
            Describe.Lean(DescribeId.Create("weilmixedheadtailbudget-inverseQuadraticEnvelope"),
                DeclarationHandle.Create(Prefix + "inverseQuadraticEnvelope"), H("Ordinate decay envelope"),
                StatementSource.FromAuthor(Disp(F.Id("u_n=1/(1+(Re gamma_n)^2)."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The real part of gamma is the actual zero ordinate. The strip displacement is not used as the ordinate."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("weilmixedheadtailbudget-fourthMomentSummand"),
                DeclarationHandle.Create(Prefix + "fourthMomentSummand"), H("Multiplicity-weighted scalar tail"),
                StatementSource.FromAuthor(Disp(F.Id("w_n=m_n*u_n^2."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exactly one analytic multiplicity factor is present per zero index."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("weilmixedheadtailbudget-finiteMixedHeadBound"),
                DeclarationHandle.Create(Prefix + "finiteMixedHeadBound"), H("A finite enclosure expression"),
                StatementSource.FromAuthor(Disp(F.Id("H_E=sum_(n in E) m_n*(sum_i plus_i(n))*(sum_j minus_j(n))."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The data bound both conjugate evaluations of each actual test. The expression includes every off-diagonal mixed term."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("weilmixedheadtailbudget-finiteMixedMajorant-head-le"),
                DeclarationHandle.Create(Prefix + "finiteMixedMajorant_head_le"), H("Finite mixed head enclosure"),
                StatementSource.FromAuthor(Disp(F.Id("Certified plus/minus transform bounds on E imply sum_E actualMixedMajorant<=H_E."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Expand the actual mixed summand, multiply nonnegative norm bounds, and factor the two finite coefficient sums."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("weilmixedheadtailbudget-finiteMixedMajorant-pointwise-decay"),
                DeclarationHandle.Create(Prefix + "finiteMixedMajorant_pointwise_decay"), H("All tail cross terms at once"),
                StatementSource.FromAuthor(Disp(F.Id("If both transform values of test i are bounded by D_i*u_n, actualMixedMajorant(n)<=(sum_i D_i)^2*w_n."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Use the existing exact polarized Fourier-Laplace factorization. Multiplicity is counted once and no cross terms are dropped."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("weilmixedheadtailbudget-finiteMixedMajorantTotal-le-head-tail"),
                DeclarationHandle.Create(Prefix + "finiteMixedMajorantTotal_le_head_tail"), H("Derived complete majorant bound"),
                StatementSource.FromAuthor(Disp(F.Id("Finite head enclosures, two-sided tail decay, and a summable scalar tail with sum<=Theta imply C_actual<=H_E+(sum_i D_i)^2*Theta."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Split the actual absolutely convergent mixed sum into E and its complement, compare the latter to the positive scalar tail, and sum. A bound on C_actual is a conclusion, not a field of a certificate. Brent-Platt-Trudgian (2021), Theorem 1, equations (1)-(3), is the literature entry for the remaining scalar tail; its numerical zeta-count estimates are not automatically imported by this theorem."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("weilmixedheadtailbudget-fourthMomentSummand-le-inverse-fourth"),
                DeclarationHandle.Create(Prefix + "fourthMomentSummand_le_inverse_fourth"), H("Interface to the published inverse-power sum"),
                StatementSource.FromAuthor(Disp(F.Id("At a nonzero ordinate t, m/(1+t^2)^2 <= m/t^4."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This supplies the envelope comparison for an inverse-fourth tail. Positive-height versus two-sided sums and endpoint half weights must still be reconciled in an application."))), DescribeRole.Theorem)), []));
}
