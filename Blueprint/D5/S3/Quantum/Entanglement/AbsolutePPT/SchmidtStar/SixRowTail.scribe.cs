using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar;
internal sealed class SixRowTailDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At every nonnegative unit five-vector, six distinct labelled K6 bottom slots have coefficient mass at least three. A six-cycle and the fifteen complementary labels give a total assignment of all twenty-one capped deficits with charge at least half their squared mass.", H("SixRowTail"), Blocks(
            Paragraph(Text("This is the constructive tail supplier at the same p used by SixRowHead.head_exists. Put z = (1,p). A diagonal slot has coefficient z_i squared and an edge slot has coefficient z_i z_j. Only the five coordinate labels are sorted by minus p; the head p and its edge labelling are retained literally. No coefficient ordering or optimizer is used.")),
            Paragraph(Text("If the sum of p is at least two, select the centre diagonal and all five centre edges. Otherwise write the sorted coordinate values as alpha, beta, gamma, delta, epsilon. Their squared sum is one and their sum is at most two. The inequalities one <= alpha times the coordinate sum and one <= alpha squared + beta times the remaining coordinate sum imply alpha + beta >= one. Bounding delta squared + epsilon squared by gamma times delta + epsilon then yields alpha + beta + gamma + alpha squared + beta squared >= two. Select the centre diagonal, the first three centre edges, and the first two successor diagonals. The six labels remain distinct even at ties and zeros.")),
            Paragraph(Text("Reverse the increasing twenty-one deficits. With t the sixth reversed entry and T the sum of the first six, every first-block square is at most x + t x - t, and every other square is at most t x. Summing all twenty-one inequalities gives q <= T + t(D - 6) <= T. Enumerate the six selected slots and their fifteen-slot complement. The six cyclic selected-block charges sum to T times the selected coefficient mass, at least 3T; one cycle has charge at least T/2. Complete this cycle with every complementary label, then reverse the resulting twenty-one indices. The selected image is exactly 15 through 20 and the complement image is 0 through 14.")),
            Paragraph(Text("The assignment covers all twenty-one bottom labels and charges the deficits at the original head vector. The selected six labels and their complement remain disjoint even when coefficients tie.")),
            Describe.Lean(DescribeId.Create("sixrowtail-sixrowtail-coefficient"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowTail.coefficient"),
                H("coefficient"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("def coefficient (p : Fin 5 → ℝ) : BottomSlot 6 → ℝ := Sum.elim (fun i => (Fin.cases 1 p i)^2) (fun e => (Fin.cases 1 p e.val.1)*(Fin.cases 1 p e.val.2))"))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sixrowtail-sixrowtail-tailcharge"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowTail.tailCharge"),
                H("tail charge"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("def tailCharge (d : Fin 21 → ℝ) (p : Fin 5 → ℝ) (σ : BottomSlot 6 ≃ Fin 21) : ℝ := ∑ B, d (σ B)*coefficient p B"))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sixrowtail-sixrowtail-six-coefficient-mass"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowTail.six_coefficient_mass"),
                H("six coefficient mass"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem six_coefficient_mass (p : Fin 5 → ℝ) (hp : ∀ i, 0 ≤ p i) (hn : ∑ i, (p i)^2=1) : ∃ S : Finset (BottomSlot 6), S.card=6 ∧ 3 ≤ ∑ B ∈ S, coefficient p B"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sixrowtail-sixrowtail-capped-tail-squares"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowTail.capped_tail_squares"),
                H("all twenty-one capped squares"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem capped_tail_squares (x : Fin 21 → ℝ) (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1) (ho : Antitone x) (hm : ∑ i, x i ≤ 6) : (∑ i, (x i)^2) ≤ ∑ i, if i.val < 6 then x i else 0"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sixrowtail-sixrowtail-tail-exists"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowTail.tail_exists"),
                H("total same-vector tail assignment"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem tail_exists (d : Fin 21 → ℝ) (p : Fin 5 → ℝ) (hd0 : ∀ i, 0 ≤ d i) (hd1 : ∀ i, d i ≤ 1) (hdo : Monotone d) (hm : ∑ i, d i ≤ 6) (hp : ∀ i, 0 ≤ p i) (hn : ∑ i, (p i)^2=1) : ∃ σ : BottomSlot 6 ≃ Fin 21, (∑ i, (d i)^2)/2 ≤ tailCharge d p σ"))), DescribeRole.Theorem)
        )));
}
