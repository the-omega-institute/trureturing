using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar;
internal sealed class SixRowHeadDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every nonnegative labelled fifteen-tuple, one nonnegative unit vector in five coordinates and one bijection of the fifteen K6 edges attain at least the Euclidean norm. Labels, rather than numerical values, are sorted, so ties remain distinct. The six final edges are assigned only after the same vector is fixed. This is a head supplier for the APPT threshold programme; it does not settle that threshold.", H("SixRowHead"), Blocks(
            Paragraph(Text("For every nonnegative labelled fifteen-tuple, one nonnegative unit vector in five coordinates and one bijection of the fifteen K6 edges attain at least the Euclidean norm. Labels, rather than numerical values, are sorted, so ties remain distinct. The six final edges are assigned only after the same vector is fixed. This is a head supplier for the APPT threshold programme; it does not settle that threshold.")),
            Paragraph(Text("The supplied constructive derivation sorts the weights as M, four b entries, four c entries and six d entries. Write X for the sum of the b squares, Y for the sum of the c squares and Z for the sum of the d squares. When Y is positive, use L = sqrt(M² + X + Z), s = M/L and t = sqrt(X + Z)/L. Normalize the four entries b_i + s c_i to a unit vector q, then choose p = (s, t q). The Lean proof uses the equivalent normalized scalar parameters alpha = M/sqrt(X), k = Y/X and h = Z/Y.")),
            Paragraph(Text("The distinguished center edge receives M. The four remaining center edges receive the b entries, and the four edges from the distinguished leaf receive the c entries. The six d labels occupy the remaining edges by a single cyclic permutation selected at the fixed q. The four-coordinate estimate directly consumes FiveRowP2Star.star_product_bound. Monotonicity in the four-coordinate norm and the exact SixRowHeadScalar.recipe_bound supply the full fifteen-entry Euclidean lower bound. When Y vanishes, all c and d entries vanish; normalization of the five center weights gives equality, with the all-zero case handled separately.")),
            Describe.Lean(DescribeId.Create("sixrowhead-sixrowhead-edgeat"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHead.edgeAt"),
                H("edgeAt"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("def edgeAt : Fin 15 → Edge 6"))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sixrowhead-sixrowhead-edgeequiv"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHead.edgeEquiv"),
                H("edgeEquiv"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("def edgeEquiv : Fin 15 ≃ Edge 6"))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sixrowhead-sixrowhead-headvalue"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHead.headValue"),
                H("headValue"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("def headValue (a : Fin 15 → ℝ) (p : Fin 5 → ℝ) (π : Edge 6 ≃ Fin 15) : ℝ"))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sixrowhead-sixrowhead-head-exists"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHead.head_exists"),
                H("head exists"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem head_exists (a : Fin 15 → ℝ) (ha : ∀ i,0 ≤ a i) : ∃ (p : Fin 5 → ℝ) (π : Edge 6 ≃ Fin 15), (∀ i,0 ≤ p i) ∧ (∑ i,(p i)^2=1) ∧ Real.sqrt (∑ i,(a i)^2) ≤ headValue a p π"))), DescribeRole.Theorem)
        )));
}
