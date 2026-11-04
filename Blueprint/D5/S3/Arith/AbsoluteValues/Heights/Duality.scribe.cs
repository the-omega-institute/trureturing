using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.AbsoluteValues.Heights;

internal sealed class DualityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Arakelov height of a subspace agrees with that of its dual annihilator.",
        H("Duality"),
        Blocks(
            Describe.Lean(DescribeId.Create("duality-ordered-enumeration"),
                DeclarationHandle.Create("D5/S3/Arith/AbsoluteValues/Heights/Duality.enumEquiv"),
                H("Selected columns followed by their complement"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For a finite linearly ordered type and a subset s of cardinality k with complement of cardinality l, enumEquiv identifies Fin k plus Fin l with the original index type. It lists s in increasing order, followed by its complement in increasing order. The exact index identification is consumed by the metallic shifted complementary-minor proof."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("duality-complementary-minor"),
                DeclarationHandle.Create("D5/S3/Arith/AbsoluteValues/Heights/Duality.det_submatrix_inl_eq_mul"),
                H("Complementary minors for dual block rows"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Let C and D be matrices over a commutative ring, with row type Fin k plus Fin l and finite ordered column type, satisfying C times transpose D equal to the identity. For a column subset s with cardinality k and complement of cardinality l, the determinant of the first block of C restricted to increasing s equals the determinant of C with its columns read through enumEquiv, multiplied by the determinant of the second block of D restricted to the increasing complement. This is the original duality declaration; the shifted Hankel boundary proof consumes it with an invertible enclosing matrix and its inverse transpose."))), DescribeRole.Theorem),
            Describe.Lean(
            DescribeId.Create("duality"),
            DeclarationHandle.Create("D5/S3/Arith/AbsoluteValues/Heights/Duality.arakelovMulHeight_comap_piEquiv_dualAnnihilator"),
            H("Duality"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("The Arakelov height of a subspace agrees with that of its dual annihilator."))),
            DescribeRole.Theorem))));
}
