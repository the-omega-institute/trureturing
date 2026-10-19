using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class AnalyticOddOccupationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/AnalyticOddOccupation.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unbounded finite-support occupations have absolutely convergent complex generating functions and ordinary Euler products inside the unit disk.",
        H("Analytic Odd Occupation"),
        Blocks(
            Paragraph(Text("An occupation d assigns a natural multiplicity to each mode and has finite support. The multiplicities have no uniform bound. For finite colours I and mode n, colouredEnergy is the sum of d(i,n)*(2*n+1), as defined in ColouredOddOccupation. Empty colours and the value q=0 are included throughout.")),
            Paragraph(Text("Mathlib supplies summable_finsetProd_of_summable_nonneg (Chris Birkbeck), Finsupp.graph_injective, geometric series, finite products of sums, and Tannery dominated convergence (David Loeffler), under Apache 2.0. Restricting the summable finite-subset family to occupation graphs is a comparison step. For 0<=r<1 and k>=1, (2*n+1)*k>=n+k bounds each nonzero graph entry by r^n*r^k. Summing the two geometric directions and the finite colours gives the all-occupation majorant.")),
            Node("summable_real_odd_occupations", "The unbounded odd-weight majorant",
                "For every finite type I, including the empty type, and every real 0<=r<1, the family d -> r^colouredEnergy(I,d) is summable over every finitely supported natural occupation on I times N. This is an estimate for all occupation multiplicities and modes.", DescribeRole.Theorem),
            Node("monomial", "Occupation monomials",
                "For an arbitrary type A, a complex mode family z:A->C and a finitely supported occupation d:A->N, monomial(z,d) is the finite product over the support of z(a)^d(a). The empty occupation has monomial one.", DescribeRole.Definition),
            Node("hasProd_inverse_eq_occupation_sum", "Complex occupation Euler expansion",
                "For any type A and complex family z with norm(z(a))<1 for every a, assume the occupation monomials are absolutely summable. Then the family a -> (1-z(a)) inverse has ordinary complex HasProd equal to the sum of all occupation monomials. On a finite set of modes, finite boxes exhaust every natural occupation and finite geometric sums converge to the inverse factors. The boxes are an exhaustion, with no fixed occupation cutoff in the conclusion. Tannery then passes from finite support restrictions to the whole occupation sum.", DescribeRole.Theorem),
            Node("summable_norm_odd_coefficients", "Absolute convergence of exact coefficients",
                "For every finite colour type I and every complex q with norm(q)<1, the family N -> norm(card(ColouredOddFiber(I,N))*q^N) is summable. The canonical colouredOddFiberEquivAntidiag gives a genuinely finite dependent partition sigma for each energy fibre. Mathlib HasSum.tsum_fiberwise groups the nonnegative majorant by precisely these fibres; no default cardinal value for infinite types enters.", DescribeRole.Theorem),
            Node("hasProd_odd_character", "The ordinary odd Euler product",
                "For every finite colour type I and every complex q with norm(q)<1, the family n -> ((1-q^(2*n+1)) inverse)^card(I) has ordinary complex HasProd equal to the sum over all N of card(ColouredOddFiber(I,N))*q^N. Occupation monomials equal q^colouredEnergy; finite-fibre regrouping identifies their sum with these exact coefficients. Every rank, empty colours and q=0 remain in scope.", DescribeRole.Theorem),
            Paragraph(Text("These are ordinary complex convergence statements. The formal coefficient series and its PowerSeries.WithPiTopology product are separate algebraic results in ColouredOddOccupation. Identifying these coefficients with dimensions of a full operator eigenspace additionally requires an exact spectral equivalence and a finite-dimensional ground space. No central charge, eta normalization, modularity, physical realization, string theory or spacetime interpretation is supplied by the analytic Euler identity."))),
        []));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("analytic-odd-occupation-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
