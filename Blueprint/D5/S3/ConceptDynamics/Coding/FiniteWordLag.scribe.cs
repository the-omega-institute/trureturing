using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class FiniteWordLagDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coupled lag witnesses for a finite rectangular word",
        H("Coupled lag witnesses for a finite rectangular word"),
        Blocks(
            Paragraph(Text("An actual ExchangeChain over any semiring carries its length and every intermediate matrix size. The source constructs a single coupled pair of lag witnesses for that whole chain; no lag or invertibility premise is added.")),
            Describe.Lean(
                DescribeId.Create("finitewordlag-1"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/FiniteWordLag.chain_lag"),
                H("Both products and both intertwiners"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For any universe-polymorphic semiring R, natural endpoint sizes n and m, length ell, matrices A of size n by n and B of size m by m, and c : ExchangeChain R A B ell, the statement returns X of size n by m and Y of size m by n with A*X=X*B, B*Y=Y*A, X*Y=A^ell and Y*X=B^ell simultaneously. Length zero, Fin 0, unequal rectangular intermediate sizes and arbitrary singular vertices remain in scope.")),
                    Paragraph(Text("The nil branch chooses both identity matrices. At a cons with factors U and V, the induction supplies X,Y for the tail and the new pair is U*X,Y*V. The tail intertwiners give the two new intertwiners; rectangular_exchange_power gives the first power product and the other intertwiner gives the second. Keeping the same witnesses in all four equations is the all-word obligation, beyond separately applying a one-cell identity.")),
                    Paragraph(Text("The existing RectangularNilpotenceBarrier.ExchangeChain and rectangular_exchange_power are reused directly. In the dyadic ladder consumer, faithful transposed coordinates turn the same pair into actual linear maps f,g with g.comp f=A^ell, f.comp g=B^ell and g.comp B=A.comp g. This source has no commutativity, domain, finite-rank, PID, unit or nonzero-dimension assumption."))),
                DescribeRole.Theorem),
            Paragraph(Text("The strongest original-h root, its finite calibrations, literal FixT6 and minimum6 are outside these finite algebraic statements. Their separate periodic and beam dictionaries and final acceptance obligations are required to close that original goal.")))));
}
