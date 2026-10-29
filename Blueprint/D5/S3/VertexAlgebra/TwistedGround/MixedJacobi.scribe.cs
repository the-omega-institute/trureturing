using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class MixedJacobiDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite actual Mobius transport for the mixed coefficient calculation",
        H("Finite actual Mobius transport for the mixed coefficient calculation"),
        Blocks(
            Paragraph(Text("The original Carrier, ActualTensor, correctedField, tensor stress L1 and inverse Gram matrix are retained. The statement concerns every original source, every signed raw exponent, every actual tensor input and every complex finite-flow parameter. It does not identify the restricted dual with the original fixed source.")),
            Paragraph(Text("The input cutoff is one plus its maximum supported odd weight. The common rectangle cutoff also exceeds the maximum supported odd weight of each corrected-field output on those finitely many lowered inputs. Input nilpotence kills columns beyond the first cutoff; actual output nilpotence kills the remaining rows. The map (i,j) to (n=i+j,i), with inverse (n,i) to (i,n-i), is used only on that bounded rectangle.")),
            Paragraph(Text("The finite diagonal sum consumes ActualMobiusAllOrder.corrected_field_mobius_coefficient. Every source energy and every original source L1 term remains in the resulting formula. Negative binomial parameters are allowed because finiteness is supplied by the actual tensor supports before reindexing, rather than inferred from a formal binomial series.")),
            Paragraph(Text("This is a repository Lean finite transport calculation using the existing formal covariance theorem. The full signed normalized two-twisted-input mixed Jacobi identity, its finite source-law substitution, and actual three-twisted crossing remain separate obligations. No classical announcement is attributed a detailed proof of this new finite calculation.")),
            Describe.Lean(DescribeId.Create("finite-actual-mobius-transport"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/MixedJacobi.finite_mobius_transport"),
                H("Finite evaluation of original all-order Mobius covariance"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two independently finite target-power sums equal a finite sum of the existing all-order source-coordinate readouts. The common cutoff is computed from the actual input and finitely many actual transformed outputs; no infinite exponential is used."))),
                DescribeRole.Theorem))));
}
