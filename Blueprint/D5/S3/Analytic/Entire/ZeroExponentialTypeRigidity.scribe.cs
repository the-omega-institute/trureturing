using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Entire;

internal sealed class ZeroExponentialTypeRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Phragmen-Lindelof damping and reflection connect growth to whole-plane constancy.", H("Rigidity at zero exponential type"),
        Blocks(
            Describe.Lean(DescribeId.Create("zero-exponential-type-rigidity-eq-at-zero-of-zero-exponential-type-of-bounded-real"),
                DeclarationHandle.Create("D5/S3/Analytic/Entire/ZeroExponentialTypeRigidity.eq_at_zero_of_zero_exponential_type_of_bounded_real"),
                H("A real-axis bound forces constancy"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an entire complex function f bounded on the entire real axis by a real B, an arbitrarily small positive exponential growth bound on the whole plane implies f(z)=f(0) at every complex z. No positivity assumption on B or on the growth constants is added. Exponential damping, Mathlib Phragmen-Lindelof on a half-plane, removal of the damping, and the bounded entire function theorem prove the claim. This root is consumed by the reflection and zero-limit root in this module."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("zero-exponential-type-rigidity-eq-zero-of-zero-exponential-type-of-reflection-of-tendsto-zero"),
                DeclarationHandle.Create("D5/S3/Analytic/Entire/ZeroExponentialTypeRigidity.eq_zero_of_zero_exponential_type_of_reflection_of_tendsto_zero"),
                H("Reflection and a vanishing ray limit"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an entire zero exponential type f with f(1-z)=f(z), convergence to zero on the full positive real ray implies f is identically zero. Reflection bounds the negative tail and continuity bounds the middle compact interval, supplying the preceding real-axis theorem. SparseQuartetProduct.reflected_difference_zero consumes this result."))), DescribeRole.Theorem),
            Paragraph(Text("The bounds quantify over every positive real epsilon and every complex point; a limit along a discrete sequence is not the stated hypothesis. These analytic implications do not assert actual-zeta or RH rigidity and do not classify minimal type. All declarations are general analytic arguments rather than any of the four computational utility classes, so utility is none. Mathlib supplies the half-plane and Liouville tools; this module supplies their damping and reflection composition without a literature-novelty claim.")))));
}
