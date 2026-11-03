using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Characters;

internal sealed class IntegerFockCharacterDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Characters/IntegerFockCharacter.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The true integer-frequency polynomial Fock energy character and finite multiplicities.",
        H("Integer Fock Character"),
        Blocks(
            Paragraph(Text("For every natural colour count r, the carrier is the full complex polynomial algebra MvPolynomial (Fin r × Nat) Complex. A variable (j,n) has energy n+1. Each polynomial has finite support, but the algebra has every positive integer frequency. No frequency cutoff, supplied dimension, or partition-count premise occurs.")),
            Node("Fock", "Full polynomial carrier", "The complex polynomial algebra on Fin r × Nat, for every natural r, including zero.", DescribeRole.Definition),
            Node("EnergyFiber", "Integer energy fibre", "For every r,N : Nat, the subtype of finitely supported exponents d : (Fin r × Nat) →₀ Nat satisfying integerEnergy (Fin r) d = N. The energy definition is the accepted AnalyticIntegerOccupation.integerEnergy, the sum of d(j,n)*(n+1). Its signed trace is not used.", DescribeRole.Definition),
            Node("PartitionTuple", "Ordinary partition tuples", "For every r,N : Nat, a dependent pair of an energy allocation e : Fin r → Nat with sum_j e(j)=N and an ordinary partition of e(j) for each colour j. These are ordinary positive-integer partitions, with the unique empty partition allowed.", DescribeRole.Definition),
            Node("grade", "Actual weighted polynomial grade", "For every r,N : Nat, the native Mathlib weightedHomogeneousSubmodule Complex (fun (j,n) => n+1) N in Fock r. Its elements are exactly polynomials whose nonzero monomial coefficients have integer energy N. The carrier is defined by polynomial support and energy, not by a desired count.", DescribeRole.Definition),
            Node("energyFiberEquivPartitionTuple", "Exact energy-preserving partition decomposition", "For every r,N : Nat, an equivalence EnergyFiber r N ≃ PartitionTuple r N. The accepted colourEquiv curries exponents by colour; conservation of integer energy identifies the sum of the one-colour energies. The accepted PolynomialFockCharacter.energyFiberEquivPartition then converts each colour to ordinary partitions. The generic dependent fibre equivalences retain all energy allocations.", DescribeRole.Theorem),
            Node("card_energyFiber", "Exact finite convolution", "For every r,N : Nat, Nat.card (EnergyFiber r N) equals the sum over e in univ.finsuppAntidiag N of the product over j : Fin r of Nat.card (Nat.Partition (e j)). The accepted energyAllocationEquivAntidiag supplies only weight-independent indexing. Finiteness follows from this actual equivalence with finite ordinary partition tuples, without assuming a finite fibre.", DescribeRole.Theorem),
            Node("gradeBasis", "Weighted monomial basis", "For every r,N : Nat, a complex basis of the actual grade r N indexed by EnergyFiber r N. Mathlib's basisRestrictSupport is transported along weightedHomogeneousSubmodule_eq_finsupp_supported; its basis vectors are the actual monomials with coefficient one. The finite energy index proves Module.Finite Complex (grade r N).", DescribeRole.Definition),
            Node("finrank_grade", "Actual finite energy dimension", "For every r,N : Nat, Module.finrank Complex (grade r N) = Nat.card (PartitionTuple r N). This dimension comes from gradeBasis and the exact fibre equivalence. It is not an assumed dimension or a fresh vector space indexed by the desired count.", DescribeRole.Theorem),
            Node("ordinaryPartitionSeries", "Ordinary partition series", "The complex formal power series whose coefficient at N is the complex cast of Nat.card (Nat.Partition N). The accepted one-colour Fock spectrum and character identify it with the product over n : Nat of (1-X^(n+1))^(-1).", DescribeRole.Definition),
            Node("character", "Actual finrank formal character", "For every r : Nat, PowerSeries.mk (fun N => (Module.finrank Complex (grade r N) : Complex)). There is no analytic convergence or vacuum-energy normalization in this definition.", DescribeRole.Definition),
            Node("character_eq_partition_power", "All-energy ordinary bosonic character", "For every natural r, character r = ordinaryPartitionSeries ^ r. The coefficient proof consumes the actual weighted-grade finrank theorem and the exact finite convolution. It includes r=0, when the character is one, and every N=0, when the dimension is one. For r=0 and positive N the dimension is zero.", DescribeRole.Theorem),
            Node("character_euler_product", "Integer Euler-product character", "For every natural r, character r equals (product over n : Nat of (1-X^(n+1))^(-1)) ^ r as a complex formal power series with the coefficient topology. The product is reused at its exact hypotheses from PolynomialFockCharacter.lZero_character_euler_product after the actual multicolour basis and dimension bridge.", DescribeRole.Theorem),
            Paragraph(Text("ColouredOddOccupation supplies only curry and antidiagonal bookkeeping. Its concrete weight 2*n+1 and odd character are different, as is the signed integer trace. This result is an independent polynomial-coordinate prerequisite for a transverse Fock character. It asserts no equivalence with original BRST cohomology, no analytic eta identity, no no-ghost theorem, and no completion of the VOA, Monster, string, or AdS/CFT programme.")))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("integer-fock-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
