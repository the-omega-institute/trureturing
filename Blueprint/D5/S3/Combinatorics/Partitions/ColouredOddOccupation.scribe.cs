using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class ColouredOddOccupationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/ColouredOddOccupation.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Odd-weight occupations are odd-part partitions with dependent finite-colour energy allocations, giving exact convolution and a formal Euler product.",
        H("Coloured Odd Occupation"),
        Blocks(
            Paragraph(Text("The variable X counts twice the half-integer oscillator energy. All finite colour types, including the empty type, and every degree are included. The coefficient identity holds over an arbitrary commutative semiring. Only the infinite-product statements use a field and its T2 topological-ring structure, with the coefficient topology on formal power series.")),
            Node("oddWeight", "Odd mode weights",
                "For every natural mode n, oddWeight(n)=2*n+1. These are positive odd parts, and this weight already counts twice the half-integer oscillator energy.", DescribeRole.Definition),
            Node("singleEnergy", "Single-colour weighted energy",
                "For every finitely supported occupation d:N -> N, singleEnergy(d) is the sum of d(n)*(2*n+1). There is no support cutoff beyond finite support of each occupation.", DescribeRole.Definition),
            Node("SingleOddFiber", "The complete single-colour fibre",
                "For every N:N, SingleOddFiber(N) consists of all finitely supported natural occupations whose singleEnergy is N.", DescribeRole.Definition),
            Node("OddPartition", "Odd-part partitions",
                "For every N:N, OddPartition(N) is the element type of Mathlib Nat.Partition.odds N, the finite set of partitions of N whose parts are all odd.", DescribeRole.Definition),
            Node("singleOddFiberEquivPartition", "Invert odd parts by integer division",
                "For every N:N, SingleOddFiber(N) is equivalent to OddPartition(N). The forward map repeats 2*n+1 with multiplicity d(n). The inverse maps each odd part j to j/2 and counts these mode indices. Positivity and odd membership give 2*(j/2)+1=j; multiset injectivity proves the other inverse. The Finsupp and multiset architecture is the one used for ordinary positive parts in PolynomialFockCharacter.energyFiberEquivPartition, with this different inverse and restricted codomain.", DescribeRole.Definition),
            Node("colouredEnergy", "Finite-colour occupation energy",
                "For every type I and occupation d:(I times N) -> N of finite support, colouredEnergy(I,d) is the weighted sum with weight 2*n+1 on a pair (i,n). I may be empty.", DescribeRole.Definition),
            Node("ColouredOddFiber", "Unbounded coloured fibre",
                "For every type I and natural N, ColouredOddFiber(I,N) is the subtype of all finitely supported occupations d with colouredEnergy(I,d)=N. All modes and occupation multiplicities are allowed.", DescribeRole.Definition),
            Node("colourEquiv", "Currying by colour",
                "For every finite type I, Mathlib Finsupp.curryEquiv followed by Finsupp.equivFunOnFinite identifies occupations on I times N with functions I -> (N -> finitely-supported N).", DescribeRole.Definition),
            Node("colouredEnergy_eq_sum", "Energy splits over colours",
                "For every finite type I and occupation d, colouredEnergy(I,d) equals the sum over i:I of singleEnergy(colourEquiv(I,d)(i)). This follows from the public Finsupp.sum_curry_index and Finsupp.sum_fintype identities.", DescribeRole.Theorem),
            Node("EnergyAllocation", "Dependent colour energies",
                "For every finite type I and N:N, EnergyAllocation(I,N) consists of functions e:I -> N whose finite sum is N.", DescribeRole.Definition),
            Node("OddPartitionSigma", "Odd partitions with dependent energies",
                "For every finite type I and N:N, OddPartitionSigma(I,N) is the dependent sum over energy allocations e of the product over i:I of OddPartition(e(i)).", DescribeRole.Definition),
            Node("pointwiseEnergyFiberEquiv", "Pointwise energy fibres",
                "For every type I and e:I -> N, the subtype of functions f:I -> (N -> finitely-supported N) with pointwise singleEnergy equal to e is equivalent to the dependent product over i of SingleOddFiber(e(i)). Mathlib subtypePiEquivPi supplies the pointwise subtype transport.", DescribeRole.Definition),
            Node("colouredOddFiberEquivSigma", "The full dependent coloured equivalence",
                "For every finite type I, including the empty type, and every N:N, ColouredOddFiber(I,N) is equivalent to OddPartitionSigma(I,N). Currying splits the actual weighted energy, sigmaSubtypeFiberEquivSubtype groups by the entire energy allocation, and the single-colour inverse is applied in every dependent fibre.", DescribeRole.Definition),
            Node("energyAllocationEquivAntidiag", "The exact finite antidiagonal",
                "For every finite decidable type I and N:N, EnergyAllocation(I,N) is equivalent to the element type of univ.finsuppAntidiag(N). The maps are Finsupp.equivFunOnFinite and evaluation, with the same sum N and full finite support condition.", DescribeRole.Definition),
            Node("colouredOddFiberEquivAntidiag", "Occupation fibres match convolution indices",
                "For every finite decidable type I and N:N, the complete occupation fibre is equivalent to the dependent sum over univ.finsuppAntidiag(N) of the products of OddPartition(e(i)). This finite sigma type also gives genuine finiteness of the original fibre.", DescribeRole.Definition),
            Node("card_colouredOddFiber", "Exact all-degree cardinal convolution",
                "For every finite decidable type I and N:N, Nat.card(ColouredOddFiber(I,N)) is the sum over e in univ.finsuppAntidiag(N) of the product over i:I of card(Nat.Partition.odds(e(i))). The equivalence with a finite dependent sigma proves the cardinal formula; no infinite-type default for Nat.card is used.", DescribeRole.Theorem),
            Node("oddPartitionSeries", "One-colour partition series",
                "For every commutative semiring R, oddPartitionSeries(R) is the formal power series whose coefficient of degree N is card(Nat.Partition.odds N), cast into R.", DescribeRole.Definition),
            Node("colouredFiberSeries", "The occupation counting series",
                "For every commutative semiring R and finite type I, colouredFiberSeries(R,I) has degree N coefficient Nat.card(ColouredOddFiber(I,N)), cast into R.", DescribeRole.Definition),
            Node("colouredFiberSeries_eq_prod", "Coefficient convolution identifies the series",
                "For every commutative semiring R and finite type I, colouredFiberSeries(R,I) equals the product over I of oddPartitionSeries(R). The exact fibre cardinal sum is the finite antidiagonal in Mathlib PowerSeries.coeff_prod. This is an algebraic coefficient identity and needs no topology.", DescribeRole.Theorem),
            Node("colouredFiberSeries_eq_pow", "Equal factors give a finite power",
                "For every commutative semiring R and finite type I, colouredFiberSeries(R,I) equals oddPartitionSeries(R) raised to Fintype.card(I). The empty product is included. This finite-product identity is used in the Euler product theorem.", DescribeRole.Theorem),
            Node("odd_geometric_eq_inverse", "The formal geometric inverse",
                "Let K be a field with a T2 topology making it a topological ring. For every n:N, the formal sum over j:N of X^((2*n+1)*j) equals the power-series inverse of 1-X^(2*n+1). Its constant term is one, and Mathlib formal geometric summation proves the multiplication identity. PowerSeries K is not assumed to be a field.", DescribeRole.Theorem),
            Node("hasProd_oddPartitionSeries", "Restricted-partition formal product",
                "Let K be a field with a T2 topology making it a topological ring. In PowerSeries.WithPiTopology, the factors (1-X^(2*n+1)) inverse have HasProd oddPartitionSeries(K). Mathlib Nat.Partition.hasProd_powerSeriesMk_card_restricted is restricted to odd positive parts, its inactive factors are one, and injective reindexing by n -> 2*n gives the stated family. The restricted-partition supplier is due to Weiyi Wang in Mathlib under Apache 2.0.", DescribeRole.Theorem),
            Node("hasProd_colouredFiberSeries", "The complete finite-colour formal Euler product",
                "Let K be a field with a T2 topology making it a topological ring, and let I be any finite type. In PowerSeries.WithPiTopology, the factors ((1-X^(2*n+1)) inverse) raised to card(I) have HasProd colouredFiberSeries(K,I). The coefficient-convolution identity identifies the target with the corresponding power of the one-colour partition series. HasProd supplies Multipliable before any tprod equality is deduced. Empty colours are included. No analytic evaluation, eta transformation, modularity or physical completion is asserted.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("odd-occupation-" + name.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
