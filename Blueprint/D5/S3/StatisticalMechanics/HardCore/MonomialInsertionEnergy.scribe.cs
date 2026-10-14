using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.HardCore;

internal sealed class MonomialInsertionEnergyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/HardCore/MonomialInsertionEnergy.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/miaoyin2026matchings");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Joint occupation energies on the original finite product-activity law.",
        H("Monomial insertion energy"),
        Blocks(
            Describe.Lean(DescribeId.Create("hc-monomial-mass"),
                DeclarationHandle.Create(Prefix + "mass"), H("The original law"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each configuration has the product of its occupied activities divided by the sum over the same finite family. The definition uses total field division. A positive probability interpretation additionally requires nonempty support and positive real activities."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hc-monomial-occupation"),
                DeclarationHandle.Create(Prefix + "monomial"), H("Joint occupation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The Boolean monomial is one exactly when every marked site is occupied. Infeasible marked sets give the zero function on the legal carrier."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hc-monomial-moment"),
                DeclarationHandle.Create(Prefix + "moment"), H("Actual joint moment"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Take the moment under the original finite product law. Marking sites does not substitute a new law or a smaller generator."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hc-monomial-insertion-states"),
                DeclarationHandle.Create(Prefix + "insertionStates"), H("Empty insertion endpoints"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A permitted edge starts at a configuration lacking the selected site and ends at its insertion in the same family."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hc-monomial-dirichlet-form"),
                DeclarationHandle.Create(Prefix + "dirichlet"), H("Once-counted heat-bath form"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Multiply the two function increments along every permitted insertion by the original empty-endpoint mass, site weight and activity heat-bath factor. Each site edge is counted once."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hc-monomial-dirichlet-identity"),
                DeclarationHandle.Create(Prefix + "monomial_dirichlet"), H("Every joint occupation energy"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For a finite family closed under erasing occupied sites, the bilinear energy of two monomials is the union moment times the sum of the occupied-site deletion coefficients on their common updated sites. Insertion and erasure identify the same edges, and only a common marked site changes both monomials.")),
                    Paragraph(Text("Miao and Yin give the positive downward-closed unit-deletion monomial calculation in Section 3.2, equations (13), (21) and (22). The present identity uses the stipulated site heat-bath coefficients and extends the finite algebra to arbitrary field activities, including zeros under total division. It does not introduce a new general monomial energy principle.")),
                    Paragraph(Text("Disjoint marked sets have zero bilinear flip energy even when their covariance is nonzero. For a positive real coherent preparation, the union moments give the tangent Gram matrix and this form gives its parent-energy matrix. This mathematical correspondence supplies neither a physical energy scale, state preparation nor a joint phase-control protocol."))), DescribeRole.Theorem))));
}
