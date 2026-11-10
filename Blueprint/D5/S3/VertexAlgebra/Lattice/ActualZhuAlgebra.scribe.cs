using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class ActualZhuAlgebraDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/ActualZhuAlgebra.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/popov2026leanvoazhu");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual full unital complex Zhu algebra",
        H("Actual full unital complex Zhu algebra"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actualzhualgebra-q"),
                DeclarationHandle.Create(Prefix + "Q"),
                H("The original full additive quotient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Q(D) is exactly Carrier(D) modulo ActualZhuFinite.zhuO(D). It retains the existing quotient AddCommGroup and complex Module; no norm-four restriction, vacuum-descendant restriction, representation kernel or changed O is used."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actualzhualgebra-quotientproduct"),
                DeclarationHandle.Create(Prefix + "quotientProduct"),
                H("Actual product on the original quotient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The complex bilinear native star, composed with the quotient map, descends by Mathlib LinearMap.liftQ₂. Its two kernel inclusions are discharged by ActualZhuLeftIdeal.star_left_mem_zhuO and ActualZhuRightIdeal.star_right_mem_zhuO under positive definiteness."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actualzhualgebra-quotientproduct-mk"),
                DeclarationHandle.Create(Prefix + "quotientProduct_mk"),
                H("Representative multiplication"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The descended product of the classes of u and v is the class of their original actual star. This representative multiplication identity reduces the quotient associativity and vacuum unit laws to the corresponding identities on original states."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualzhualgebra-quotientring"),
                DeclarationHandle.Create(Prefix + "quotientRing"),
                H("Associative unital ring with the original additive group"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The multiplication is quotientProduct and one is the class of the original vacuum. The full actual associator proves associativity. The vacuum field gives the left unit; creation, creativity and the finite original energy decomposition give the right unit on every original state. The ring extends the existing quotient AddCommGroup directly. No stability or associativity hypothesis bundle is assumed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actualzhualgebra-quotientalgebra"),
                DeclarationHandle.Create(Prefix + "quotientAlgebra"),
                H("Complex algebra with the original scalar action"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Algebra.ofModule uses bilinearity of quotientProduct and the existing quotient complex Module. Scalars act by their multiples of the vacuum class, with the same additive and scalar operations as the original quotient. This construction is a possibly noncommutative algebra; commutativity is not asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actualzhualgebra-vacuum-not-mem-zhuo"),
                DeclarationHandle.Create(Prefix + "vacuum_not_mem_zhuO"),
                H("The vacuum survives the literal O"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For positive-definite D, gradeProjection(D,0) kills every circle summand: decompose the unrestricted second state into its finite nonnegative energy components q, and use the actual mode grading to put the i-th term in energy K+q-i+1, which is strictly positive for i at most K. Linearity kills the full literal span O. The same projection fixes the nonzero original vacuum, so the vacuum does not belong to O. No claim that O is graded is made."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actualzhualgebra-quotientnontrivial"),
                DeclarationHandle.Create(Prefix + "quotientNontrivial"),
                H("Nontriviality of the actual quotient algebra"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The vacuum class and zero are distinct by vacuum_not_mem_zhuO. Together with quotientRing, quotientAlgebra and the existing ActualZhuFinite.positive_definite_zhu_quotient_finite, this supplies a nonzero finite-dimensional associative unital complex algebra on exactly the original full quotient. Finite-dimensionality is reused, not reproved or renamed as new mathematical content."))),
                DescribeRole.Definition),
            Paragraph(Text("The quotient ring and algebra construction adapts ZhuRing.lean from Fedor K. Popov, Lean_VOA commit 013a799ca834a8a6b3afa8129e3e522025b3f45c, Apache-2.0. Native Lean 4.35 and its pinned Mathlib differ from upstream Lean 4.30 and its Mathlib pin, as recorded in the reference note. Native Mathlib supplies generic bilinear quotient descent, and all original lattice field, grading, star, literal circle span, two ideal stabilities and associator proofs are reused. This is a literature-attested native port. The grade-zero separation argument retains the exact literal O, not a representation kernel.")),
            Paragraph(Text("The dependent-family audit remains incomplete: exact source reconstruction, an enrolled readout, the actual-positive law, whole-family variation and sensitivity, actual observational dependence and current source binding are still required. See https://github.com/the-omega-institute/trureturing/issues/28745.")))));
}
