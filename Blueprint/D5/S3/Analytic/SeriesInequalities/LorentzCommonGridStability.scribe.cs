using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.SeriesInequalities;

internal sealed class LorentzCommonGridStabilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/SeriesInequalities/LorentzCommonGridStability.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Estimation/holtznazarovperes2011smoothcoins");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One actual Lorentz recursion has joint degree, Holder, next-derivative and residual bounds.",
        H("Common-grid Lorentz stability"),
        Blocks(
            Paragraph(Text("Write I=[0,1], delta(n,x)=max(sqrt(x(1-x)/n),1/n), and Q(n,r,f) for the actual Lorentz operator applied to the derivatives of f within I. For natural tau,b,r, define C(0)=Q(tau,r,f) and C(j+1)=C(j)+Q(tau*b^(j+1),r,f-C(j)). Polynomial evaluation in this recurrence uses the real point embedded in the complex numbers.")),
            Paragraph(Text("For r<beta<r+1 there are a natural B at least 2 and positive real U,V,E, chosen before b, tau and f. For every b at least B, every positive tau, every complex-valued f that is C^r on I and every nonnegative H bounding the beta-r Holder seminorm of its rth derivative, the following four conclusions hold simultaneously for every j and the same C(j). Its degree is at most tau*b^j+r. Its rth derivative has Holder seminorm at most U*H. Its (r+1)st derivative has modulus at most V*H*delta(tau*b^j,x)^(beta-r-1). For every nu at most r, the nu-th residual derivative has modulus at most E*H*delta(tau*b^j,x)^(beta-nu). All pointwise conclusions include both endpoints.")),
            Paragraph(Text("This is a repository deduction extending the common-center argument in Holtz, Nazarov and Peres, Section 5, Steps 1–3, to the stated complex-valued seminorm hypotheses and common quantifiers. The two-scale estimate compares near and distant pairs before choosing one refinement threshold. It supplies no Bernstein coefficient bound for the real increment kernel and no tensor compatibility statement.")),
            Entry("residual-jet", "residual_jet", "Residual jet",
                "For j<=r and x in [0,1], the jth derivative within the interval of f minus a complex polynomial is the derivative of f minus the evaluated jth polynomial derivative. The input f is C^r on the closed interval."),
            Entry("operator-residual", "operator_residual", "Operator residual",
                "For a positive sampling degree and a C^r input, applying the actual Lorentz operator to f minus a polynomial equals the operator of f minus the polynomial Lorentz operator. This identity is consumed by the common-grid recurrence."),
            Entry("common-grid-stability", "common_grid_stability", "Common grid stability",
                "All four estimates and their quantifier order are as stated above. H=0, arbitrary positive initial grids, and both endpoints are included; lower-derivative uniform norms are not assumed."))));

    private static DocumentBlock Entry(string id, string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
