using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class FourPortHeatRealizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/FourPortHeatRealization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full heat kernel of a complete four-port network has linear order seven and physical order eight.",
        H("A physical order gap for four marked heat ports"),
        Blocks(
            Describe.Lean(DescribeId.Create("cycle-gram-width"),
                DeclarationHandle.Create(Prefix + "cycle_gram_width"),
                H("Four columns are necessary under the cycle bounds"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let A have four rows in cyclic order, m columns and nonnegative real entries. Suppose AAᵀ has diagonal entries at most 4, cyclic entries Q₀₁, Q₁₂, Q₂₃ and Q₃₀ at least 1, and opposite entries Q₀₂ and Q₁₃ strictly below 1/36. Then m is at least four.")),
                    Paragraph(Text("With at most three columns, each cyclic entry has a contributing column whose endpoint product is at least 1/3. The diagonal cap bounds each factor entry by 2, so both endpoints in the chosen column have entries at least 1/6. Two edges choose the same column, and their endpoint union contains an opposite pair. That column contributes at least 1/36 to the opposite entry.")),
                    Paragraph(Text("For the unperturbed incidence Gram matrix the triangle-free support argument is classical. See Naomi Shaked-Monderer, Bounding the CP-rank by graph parameters, Electronic Journal of Linear Algebra 28 (2015), DOI 10.13001/1081-3810.3009. The bound here also permits positive opposite entries."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cycle-heat-order-gap"),
                DeclarationHandle.Create(Prefix + "cycle_heat_order_gap"),
                H("The complete example has physical order eight and linear order seven"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("There are four labeled ports and four hidden vertices, all with unit mass. The cross conductance matrix is the unsigned cycle incidence matrix plus the all-ones matrix divided by 1000. The incidence rows are (1,0,0,1), (1,1,0,0), (0,1,1,0), and (0,0,1,1). Each distinct pair on the same side has conductance 1/1000. The symmetric generator S has zero row sums and strictly negative off-diagonal entries.")),
                    Paragraph(Text("For a physical candidate write z for the vector of positive square roots of the masses with value one at each port. Its mass-normalized generator S is symmetric, annihilates z and has nonpositive off-diagonal entries. These conditions give the conductance Laplacian diag(z) S diag(z). The port insertion E gives moments Uⱼ = Eᵀ Sʲ E and heat kernel Eᵀ exp(−tS) E.")),
                    Paragraph(Text("Block multiplication identifies the defect Q = U₂ − U₁² with AAᵀ for the nonnegative cross block A = −S_PH. For the stated network Q has values 2+q on the diagonal, 1+q on cycle edges and q on opposite pairs, where q = 1001/250000. Every physical candidate within entrywise defect error 1/250 obeys the cycle bounds and therefore has at least eight vertices. The same lower bound applies to exact heat data because the first and second derivatives at zero determine U₁ and U₂.")),
                    Paragraph(Text("The hidden hyperplane x₀ − x₁ + x₂ − x₃ = 0, together with the port space, is invariant under S. Restricting to it preserves all port moments and the entire matrix exponential readout. For the converse, take the four port columns of E and the first three columns of SE. They have rank seven by a nonzero minor. Their Gram matrix is the corresponding principal section of the two-step moment Hankel matrix. For any linear realization with the same heat curve this section factors through the state space, so its dimension is at least seven.")),
                    Paragraph(Text("The dimension includes the stationary mode. The perturbation statement concerns physical order in a band on the first-two-moment defect. Its hypothesis is at the calibrated heat-moment level."))),
                DescribeRole.Theorem))));
}
