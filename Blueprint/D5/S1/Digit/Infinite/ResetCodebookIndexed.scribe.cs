using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Infinite;

internal sealed class ResetCodebookIndexedDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/Infinite/ResetCodebookIndexed.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reset codebooks, actual sources and weighted lower-memory graphs.",
        H("Reset codebook: Indexed"),
        Blocks(
            Node("pastRec", "pastRec", "pastRec", "The mathematical data are specified by pastRec(w : ℤ→Bool) (i : ℤ) : ℕ→ℝ→ℝ | 0,z => z | n+1,z => Statement.f (w (i-1)) (pastRec w (i-1) n z) noncomputable def stateRec (w : ℤ→Bool) (i : ℤ) := ⨆ n, pastRec w i n 0.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("stateRec", "stateRec", "stateRec", "The mathematical data are specified by stateRec(w : ℤ→Bool) (i : ℤ) := ⨆ n, pastRec w i n 0.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("stateRec_limit", "stateRec_limit", "stateRec limit", "For the specified parameters, the following hypotheses imply the stated relation: (w : ℤ→Bool) (i : ℤ) : Filter.Tendsto (fun n => pastRec w i n 0) Filter.atTop (nhds (stateRec w i))", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("stateRec_interval", "stateRec_interval", "stateRec interval", "For the specified parameters, the following hypotheses imply the stated relation: (w : ℤ→Bool) (i : ℤ) : 0 ≤ stateRec w i ∧ stateRec w i ≤ h false", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("stateRec_next", "stateRec_next", "stateRec next", "For the specified parameters, the following hypotheses imply the stated relation: (w : ℤ→Bool) (i : ℤ) : stateRec w (i+1)=Statement.f (w i) (stateRec w i)", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("XMinus", "XMinus", "XMinus", "The mathematical data are specified by XMinus(K n : ℕ) (tau : ℝ) : Set (ℤ → Bool) := .", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("aux_mem_XMinus", "aux_mem_XMinus", "aux mem XMinus", "For the specified parameters, the following hypotheses imply the stated relation: (K n : ℕ) (tau eps : ℝ) (w : ℤ → Bool) (hcap : Statement.cap K w) (hmargin : ∀ i, Statement.high K w i → tau + eps ≤ D5.S1.Digit.Infinite.ResetCodebook.stateRec w i) (heps : 0 < eps) (hcut : h false * rho^n < eps) : w ∈ XMinus K n tau", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("past_eq_pastRec", "past_eq_pastRec", "past eq pastRec", "For the specified parameters, the following hypotheses imply the stated relation: (w : ℤ → Bool) (i : ℤ) (n : ℕ) (z : ℝ) : Statement.past w i n z = pastRec w i n z", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("state_eq_stateRec", "state_eq_stateRec", "state eq stateRec", "For the specified parameters, the following hypotheses imply the stated relation: (w : ℤ → Bool) (i : ℤ) : Statement.state w i = stateRec w i", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lowerLanguage_eq_XMinus", "lowerLanguage_eq_XMinus", "lowerLanguage eq XMinus", "For the specified parameters, the following hypotheses imply the stated relation: (K n : ℕ) (d : ℝ) : Statement.lowerLanguage K n d = XMinus K n (chi^(K-1)*d)", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("letters_end_false", "letters_end_false", "letters end false", "For the specified parameters, the following hypotheses imply the stated relation: (a : Return) (as : List Return) : ∃ u : List Bool, Statement.letters (a::as) = u ++ [false]", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("weak_word_local_guard", "weak_word_local_guard", "weak word local guard", "For the specified parameters, the following hypotheses imply the stated relation: (w : ℤ → Bool) (p : ℤ) (K : ℕ) (q : ℝ) (as : List Return) (hw : Statement.weak K q as (stateRec w p)) (hprev : w (p-1)=false) (hu : ∀ j : Fin (Statement.letters as).length, w (p+(j.val:ℤ))=(Statement.letters as)[j.val]) : ∀ i : ℤ, p ≤ i → i < p+((Statement.letters as).length:ℤ) → ¬Statement.high (K+1) w i ∧ (Statement.high K w i → chi^(K-1)*q ≤ stateRec w i)", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("concatenation_cap_margin", "concatenation_cap_margin", "concatenation cap margin", "Every bilateral concatenation of the complete weak equal-weight codebook with the fixed reset obeys the cap. Its finite-past evaluations tend to its state, and every high departure state is at least chi^(K-1)*d plus the same positive quantity chi^(K-1)*(B(M)-D0)*g^N.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("reset_complete_family_membership", "reset_complete_family_membership", "reset complete family membership", "For the specified parameters, the following hypotheses imply the stated relation: (anchor : Bool) (K M N : ℕ) (b d : ℝ) (hK : 2 ≤ K) (hM : 1 ≤ M) (hb : lambda-g^2*chi^K*h false < b) (hd : d = (lambda-b)/(g^2*chi^K)) (hreset : max (X false) (Y false) < Statement.B M) : 0 < Statement.actualEps anchor K M N b ∧ Statement.finiteActual anchor K M N b d hM ∧ ∃ n : ℕ, K ≤ n ∧ h false*rho^n < chi^(K-1)*(Statement.B M-initial false anchor)*g^N ∧ ∀ w, Statement.concatenation anchor K M N d hM w → w ∈ Statement.lowerLanguage K n d", DescribeRole.Theorem, AssessedProvenance.FromRepo())
        )));

    private static DocumentBlock Node(string declaration, string identifier, string title, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("resetcodebookindexed-" + identifier.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), provenance,
            Blocks(Paragraph(Text(prose))), role);
}
