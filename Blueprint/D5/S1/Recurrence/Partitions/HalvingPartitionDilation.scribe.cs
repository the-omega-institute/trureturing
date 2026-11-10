using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Partitions;

internal sealed class HalvingPartitionDilationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Partitions/HalvingPartitionDilation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Automata/mazhang2026weightedhalving");

    private static readonly LibraryNoteRef Alekseyev =
        LibraryNoteRef.Create("D5/L/Words/alekseyev2026halving");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "HalvingPartitionDilation", H("HalvingPartitionDilation"), Blocks(
            Paragraph(Text("The newly public declarations in this source owner have unfinished information-escape audits: complete mirrored realization, variation, sensitivity, observational dependence and current source-binding evidence are missing. The exact per-target records and missing evidence are listed in https://github.com/the-omega-institute/trureturing/issues/28691 under CLAUDE section 3.9. This audit exception supplies no mathematical proof or independent final acceptance.")),
            Paragraph(Text("At positive even input 2n the first part is forced to be n. Removing or prepending that exact first part is a bijection of the original source lists. This proves even dilation for all inputs, including zero via the existing count-zero result, and supplies the later Stern-deficit dilation. Alekseyev (2026), Theorem 5, Lemma 2 and Corollary 15 retain their antecedent credit; OEIS antecedents are Kimberling and Heinz. The later note is by Haobo Ma then Wenlin Zhang, CC BY 4.0. General deficit digit formulas, exact fixed-length maxima, general weighted coefficients, other partition bases, A349553 minimal inputs and general-input unimodality remain open. Existing atlas-lean and Mathlib licenses are retained; no global novelty claim is made.")),
            Node("evenSourceEquiv", "Exact source declaration: def evenSourceEquiv (n : ℕ) (hn : 0 < n) : SourceLists n ≃ SourceLists (2 * n) where toFun p := ⟨n :: p.val, by refine ⟨?_, ?_, ?_⟩ · intro x hx simp only [List.mem_cons] at hx rcases hx with rfl | hx · exact hn · exact p.prop.1 x hx · simp [p.prop.2.1, two_mul] · exact ⟨Or.inl (by omega), p.prop.2.2⟩⟩ invFun p := ⟨p.val.tail, by have hhead : ∃ xs, p.val = n :: xs := by cases he : p.val with | nil => have hs := p.prop.2.1; rw [he] at hs; simp only [List.sum_nil] at hs; omega | cons x xs => have hf := p.prop.2.2 rw [he] at hf have hx : x = n := by rcases hf.1 with h | h <;> omega exact ⟨xs, by rw [hx]⟩ obtain ⟨xs, hxs⟩ := hhead have hs := p.prop.2.1 have hf := p.prop.2.2 rw [hxs] at hs hf ⊢ simp only [List.tail_cons] refine ⟨fun x hx => p.prop.1 x (by simp [hxs, hx]), ?_, hf.2⟩ simp only [List.sum_cons] at hs simpa only [List.tail_cons] using (show xs.sum = n by omega)⟩ left_inv p := by apply Subtype.ext; rfl right_inv p := by apply Subtype.ext cases he : p.val with | nil => have hs := p.prop.2.1; rw [he] at hs; simp only [List.sum_nil] at hs; omega | cons x xs => have hf := p.prop.2.2 rw [he] at hf have hx : x = n := by rcases hf.1 with h | h <;> omega simpa only [he, List.tail_cons] using congrArg (fun k => k :: xs) hx.symm", DescribeRole.Definition),
            Node("count_even", "Exact source declaration: theorem count_even (n : ℕ) : count (2 * n) = count n", DescribeRole.Theorem),
            Node("count_even_dilation", "Exact source declaration: theorem count_even_dilation (n v : ℕ) : count (2 ^ v * n) = count n", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string statement, DescribeRole role) => Describe.Lean(
        DescribeId.Create("halvingpartitiondilation-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(name), StatementSource.WithoutFormula(),
        name is "count_even" or "count_even_dilation"
            ? AssessedProvenance.FromLiterature(Alekseyev) : AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(statement))), role);
}
