using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Oscillation;

internal sealed class FejerDirichletTransferDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Logarithmic oscillation from a paired Laplace pole expansion.",
        H("Fejer and Dirichlet transfer"),
        Blocks(Describe.Lean(
            DescribeId.Create("quantitative-fejer-dirichlet-transfer"),
            DeclarationHandle.Create(
                "D5/S3/Analytic/Oscillation/FejerDirichletTransfer.quantitative_fejer_dirichlet_transfer"),
            H("Two signs at logarithmic scale"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let S be a locally finite family of distinct positive ordinates with "
                    + "positive integer multiplicities. Assume its multiplicity count N(T), "
                    + "divided by T log T, tends to 1/(2 pi). Let f be measurable and locally "
                    + "bounded on the nonnegative ray. Suppose its Laplace transform initially "
                    + "converges absolutely to a paired pole expansion with residues equal to "
                    + "minus one half of the multiplicities. The remaining function is "
                    + "holomorphic on a strip across the imaginary axis and has polynomial "
                    + "growth there, as specified by PairedLaplaceData. Then some c>0 has "
                    + "the following property: above every real threshold there is y>1 with "
                    + "f(y) at most -c log y, and there is y>1 with f(y) at least c log y.")),
                Paragraph(Text(
                    "Set p=max(k,1). Dirichlet simultaneous approximation with Q=8 aligns "
                    + "each chosen finite family of phases at a center y between "
                    + "M^(p+3) and M^(p+3) times 8 to the number of distinct phases. "
                    + "Every aligned cosine is at least cos(pi/4). On the negative side, "
                    + "use all ordinates up to M and the Fejer kernel K_M. Its triangular "
                    + "spectral mass Wminus is asymptotic to M log M/(4 pi). The phase "
                    + "count is at most N(M), so log(exp(1)+y) is bounded by a fixed "
                    + "multiple of Wminus.")),
                Paragraph(Text(
                    "For the positive side, choose b>0 below every ordinate. The upper "
                    + "band selection theorem gives U in [T,2T] with triangular window "
                    + "mass Wplus at least cb log T and total window multiplicity at "
                    + "most twelve times Wplus. Put M=U+b and align only ordinates "
                    + "with abs(gamma-U)<b. The notched kernel H_(b,U) has transform "
                    + "minus one half of the triangular weight on this window, since "
                    + "the unshifted and oppositely shifted triangles vanish at every "
                    + "ordinate. Thus its boundary main term is positive, at least "
                    + "cos(pi/4) times Wplus divided by two. Again log(exp(1)+y) is "
                    + "at most a fixed multiple of the selected mass.")),
                Paragraph(Text(
                    "If either required sign failed eventually, local boundedness would "
                    + "extend the resulting single-sided logarithmic bound to a global "
                    + "bound with an additive constant. The quantitative boundary formula "
                    + "then applies. Its error is bounded for the selected centers because "
                    + "y is at least M^(p+3) and the counting asymptotic bounds N(2M) "
                    + "by a constant times M squared. Positivity, unit kernel mass, and "
                    + "the corresponding logarithmic average estimate give a conflicting "
                    + "bound on the convolution when the assumed logarithmic coefficient "
                    + "is chosen sufficiently small. The two contradiction arguments "
                    + "supply positive constants; their minimum works for both signs. "
                    + "This is a conditional transfer theorem and does not assert RH, "
                    + "a matching upper bound, or a restriction to integer centers."))),
            DescribeRole.Theorem))));
}
