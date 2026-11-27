using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicComparison.Primitive;

internal sealed class PrimitivePeriodsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Primitive Periods", H("Primitive Periods"),
        Blocks(
            Paragraph(Text("Primitive comparison modulo p lifts to period-ring coefficients.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicComparison/Primitive/PrimitivePeriods.exists_primitive_period_comparison"),
                H("exists_primitive_period_comparison"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Primitive comparison: let (S, K) satisfy IsPeriodRingPair, K flat over S, Ψ ≅ K ⊗ (S ⊗ W(c^♭))^ on p-adic tests c. The natural map K ⊗ W(LC(Spec c[1/p], 𝔽_p)) → Ψ is bijective on cohomology along α: N' → N if N, N' have flat base change, all Hⁿ(N, ℤ_p) are finitely generated, and primitiveMap ⊗ (S/p) ⊗ 𝔪 is.")))))));
}
