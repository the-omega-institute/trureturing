using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.SubgroupGenerating;

internal sealed class EnergyBoundsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/SubgroupGenerating/EnergyBounds.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGroups/das2026sgb");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full finite-nonabelian ten-clause conclusion.", H("EnergyBounds"), Blocks(
            Describe.Lean(DescribeId.Create("sgb-energybounds-sgb-energy"),
                DeclarationHandle.Create(Owner + "sgb_energy"), H("Four exact globally centered energies"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every finite group let M=card(G)^2, k=card(Subgroup G), t=card(positiveFibers), and d=2M/(M+k). The literal adjacency energy is 2 sum_H sqrt(r_H); CN energy is 2(M-t); LE is k*d+(M-t)*abs(1-d)+M+t-t*d; and the signless energy equals LE. The actual edge count gives this single center d for the whole carrier, and 0<=d<2. Isolates contribute d to each centered energy. No component-specific center is used."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sgb-energybounds-adjacency-not-integral"),
                DeclarationHandle.Create(Owner + "adjacency_not_integral"), H("A noninteger actual adjacency eigenvalue"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every finite group of order greater than one, the actual adjacency spectrum is not integral. A Cauchy subgroup of prime order p contributes sqrt(p^2-1). This value lies strictly between p-1 and p, so it cannot equal any integer. Membership in the actual spectrum follows from the complete block-spectrum theorem."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sgb-energybounds-other-spectra-integral"),
                DeclarationHandle.Create(Owner + "other_spectra_integral"), H("The other three integral spectra"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every finite group and each matrix kind other than adjacency, every member of the actual graph spectrum is an integer. The star lists and their complete multiset sum give the integer witnesses, including zero fibers."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sgb-energybounds-result"),
                DeclarationHandle.Create(Owner + "result"), H("The full finite-nonabelian ten-clause conclusion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every group G with finite underlying set and a pair a,b satisfying a*b != b*a, all ten displayed clauses hold simultaneously for the literal sgbGraph G. The carrier is (G x G) disjoint-union Subgroup G, with all ordered and repeated pairs and all subgroups. A, L=D-A, Q=D+A and zero-diagonal common-neighbor counts are the existing source matrices; the spectra are their real Hermitian eigenvalues with algebraic multiplicity. Integral means every eigenvalue equals an integer. The energy uses the whole graph center only for L and Q. The adjacency spectrum is not integral, while L, Q and CN have integral spectra. In addition, E<n, E<=2(n-1), LE<=2(n-1), LEplus<=2(n-1), ECN<=2(n-1)(n-2), and E<=LE all hold. The prime fiber makes 2sqrt(r)<r+1 strict in the sum for E<n. For d<=1, LE=2kd and M<=k give both bounds. For d>=1, LE=2M-2t(d-1), and the group square-root deficit gives E<=LE since d<2. The CN bound uses k,t>=1. The statement uses the displayed scalar bounds for the complete-graph benchmarks. The original paper explicitly defines Q=D+A but has nearby prose saying D; this result retains the explicit matrix definition and makes no author-correction claim."))), DescribeRole.Theorem, new OpenProblemResolutionClaim(ProblemSlugRef.Create("das-2026-nonabelian-sgb-problem49"), ResolutionKind.Proved)))));
}
