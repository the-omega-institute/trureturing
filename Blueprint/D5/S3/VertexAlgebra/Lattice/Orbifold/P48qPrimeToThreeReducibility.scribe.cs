using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold;

internal sealed class P48qPrimeToThreeReducibilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/Orbifold/P48qPrimeToThreeReducibility.";
    private static readonly LibraryNoteRef Nebe =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/nebe2014extremal48");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every faithful rational representation in dimension 48 of a subgroup of SL₂(F₄₇) whose order is prime to three has a nonzero proper invariant subspace.",
        H("Rational Reducibility for Prime-to-Three Subgroups of SL₂(F₄₇)"),
        Blocks(
            Paragraph(Text("Nebe identifies the automorphism group of the rank-48 extremal lattice P48q in Table 1 of arXiv:1312.3780. "
                + "The reducibility argument concerns rational representations of its subgroups.")),
            Describe.Lean(
                DescribeId.Create("cyclotomic-degree-divides-dimension"),
                DeclarationHandle.Create(Prefix + "prime_sub_one_dvd_finrank_of_ker_sub_one_eq_bot"),
                H("Cyclotomic degree divides rational dimension"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let p be prime and let T be a rational linear endomorphism with Tᵖ = 1 and ker(T − 1) = 0. "
                    + "Then p − 1 divides the rational finrank. Factoring Xᵖ − 1 and using injectivity of T − 1 shows that "
                    + "the p-th cyclotomic polynomial annihilates T. The resulting action of the cyclotomic field makes its degree p − 1 a divisor of the finrank."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("order-bound-or-normal-cyclic-subgroup"),
                DeclarationHandle.Create(Prefix + "card_le_32_or_exists_normal_zpowers"),
                H("An order bound or a normal cyclic subgroup"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A finite group whose order divides 32 × 23 × 47 has order at most 32 or has a normal cyclic subgroup of order 23 or 47. "
                    + "If 47 divides the order, the number of Sylow 47-subgroups divides 32 × 23 and is congruent to one modulo 47. "
                    + "Only one meets both conditions. After excluding 47, the same argument uses divisors of 32 modulo 23."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reducibility-from-order-divisibility"),
                DeclarationHandle.Create(Prefix + "exists_invariant_subspace_of_card_dvd"),
                H("An invariant subspace from the order divisor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let a finite group of order dividing 32 × 23 × 47 act faithfully on a 48-dimensional rational vector space. "
                    + "For order at most 32, the orbit span of a nonzero vector is invariant and has dimension at most 32. "
                    + "Otherwise the fixed space of the normal cyclic subgroup is invariant. It is nonzero because neither 22 nor 46 divides 48, "
                    + "and proper because the action is faithful."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-to-three-sl47-reducibility"),
                DeclarationHandle.Create(Prefix + "sl47_prime_to_three_exists_invariant_subspace"),
                H("Reducibility for subgroups of SL₂(F₄₇)"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Nebe),
                Blocks(Paragraph(Text("Let H be a subgroup of SL₂(F₄₇) with order prime to three. "
                    + "Every faithful rational representation of H of dimension 48 has a nonzero proper subspace preserved by every element of H. "
                    + "The ambient order is 3 × 32 × 23 × 47. The subgroup order divides it and is coprime to three, so the previous order-divisibility result applies."))),
                DescribeRole.Theorem))));
}
