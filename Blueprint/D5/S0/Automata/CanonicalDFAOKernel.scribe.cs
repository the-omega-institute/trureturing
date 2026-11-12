using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Automata;

internal sealed class CanonicalDFAOKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Automata/CanonicalDFAOKernel.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Automata/mazhang2026weightedhalving");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "CanonicalDFAOKernel", H("CanonicalDFAOKernel"), Blocks(
            Paragraph(Text("The newly public declarations in this source owner have unfinished information-escape audits: complete mirrored realization, variation, sensitivity, observational dependence and current source-binding evidence are missing. The exact per-target records and missing evidence are listed in https://github.com/the-omega-institute/trureturing/issues/28691 under CLAUDE section 3.9. This audit exception supplies no mathematical proof or independent final acceptance.")),
            Paragraph(Text("Finite canonical MSDF output machines have finite arithmetic kernels. Correctness is assumed only for positive canonical expansions; the proof treats the zero input separately and imposes no padding or zero-output convention. The adopted all-word LSDF equivalence is a different, explicitly named supplier. Alekseyev (2026), Theorem 5, Lemma 2 and Corollary 15 retain their antecedent credit; OEIS antecedents are Kimberling and Heinz. The later note is by Haobo Ma then Wenlin Zhang, CC BY 4.0. General deficit digit formulas, exact fixed-length maxima, general weighted coefficients, other partition bases, A349553 minimal inputs and general-input unimodality remain open. Existing atlas-lean and Mathlib licenses are retained; no global novelty claim is made.")),
            Paragraph(Text("The standard canonical digit definition is relocated verbatim from AntiRecurrenceAutomaticity into this common S0 dependency, preserving its original fully qualified name. The original recurrence owner and the kernel correspondence both directly use that one definition; no duplicate or forwarding definition is introduced.")),
            Node("msfDigits", "D5/S1/Recurrence/AntiRecurrenceAutomaticity.msfDigits", "Exact source declaration: def msfDigits (b : ℕ) (hb : 0 < b) (n : ℕ) : List (Fin b) := (Nat.digits b n).reverse.map (fun d => ⟨d % b, Nat.mod_lt d hb⟩)", DescribeRole.Definition),
            Node("CanonicalAutomatic", Prefix + "CanonicalAutomatic", "Exact source declaration: def CanonicalAutomatic {B : Type*} (k : ℕ) (hk : 2 ≤ k) (a : ℕ → B) : Prop := ∃ Q : Type, ∃ _ : Fintype Q, ∃ M : DFAO (Fin k) B Q, ∀ n, 0 < n → M.evalOutput (msfDigits k (by omega) n) = a n", DescribeRole.Definition),
            Node("canonical_finite_kernel", Prefix + "canonical_finite_kernel", "Exact source declaration: theorem canonical_finite_kernel {B : Type*} (k : ℕ) (hk : 2 ≤ k) (a : ℕ → B) (ha : CanonicalAutomatic k hk a) : Finite ↥(kKernel k a)", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string declaration, string statement, DescribeRole role) => Describe.Lean(
        DescribeId.Create("canonicaldfaokernel-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(declaration), H(name), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(statement))), role);
}
