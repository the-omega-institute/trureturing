using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class FiniteMixedWeilMajorantDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/ZetaBridge/FiniteMixedWeilMajorant.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All mixed convolution terms of a finite Weil basis are absolutely summable and yield one majorant uniform over the whole coefficient space.",
        H("Finite Mixed Weil Majorant"),
        Blocks(
            Describe.Lean(DescribeId.Create("finite-weil-synthesis-full-mixed-expansion"),
                DeclarationHandle.Create(Prefix + "zeroSummand_finite_synthesis_expansion"),
                H("The square includes every coefficient cross term"),
                StatementSource.FromAuthor(Disp(F.Id("s_n(sum a_i g_i) = sum_i sum_j a_i conjugate(a_j) mixedSummand_ij(n)"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The mixed summand is the actual zero summand of convolve(g_i,involution(g_j)), so its absolute summability comes from the existing zeta explicit formula. No diagonal-only estimate is substituted for a bound on the full family."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-weil-family-uniform-absolute-majorant"),
                DeclarationHandle.Create(Prefix + "finite_synthesis_absolute_sum_le"),
                H("One fixed majorant controls every coefficient vector"),
                StatementSource.FromAuthor(Disp(F.Id("sum_n norm(s_n(a)) <= finiteComplexEnergy(a) * C_basis"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each coefficient product has norm at most the complete coefficient energy. Summing all mixed absolute terms gives a finite constant independent of the coefficient vector and of later convolution-power depth."))),
                DescribeRole.Theorem)), []));
}
