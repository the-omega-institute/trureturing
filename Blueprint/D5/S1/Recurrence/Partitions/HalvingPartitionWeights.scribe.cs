using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Partitions;

internal sealed class HalvingPartitionWeightsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Partitions/HalvingPartitionWeights.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Automata/mazhang2026weightedhalving");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "HalvingPartitionWeights", H("HalvingPartitionWeights"), Blocks(
            Paragraph(Text("The newly public declarations in this source owner have unfinished information-escape audits: complete mirrored realization, variation, sensitivity, observational dependence and current source-binding evidence are missing. The exact per-target records and missing evidence are listed in https://github.com/the-omega-institute/trureturing/issues/28691 under CLAUDE section 3.9. This audit exception supplies no mathematical proof or independent final acceptance.")),
            Paragraph(Text("Weights and lengths are read from the same actual positive ordered lists, with virtual predecessor n, repeated terminal ones and the unique empty list at zero. Integer step digits are p_(i-1)-2*p_i+1; the exponent counts literal digit ones. The complete dyadic polynomial uses truncated natural exponents, so m=2 yields W_t(5)=2+t. The parameter t is arbitrary, including zero and nonunits. Alekseyev (2026), Theorem 5, Lemma 2 and Corollary 15 retain their antecedent credit; OEIS antecedents are Kimberling and Heinz. The later note is by Haobo Ma then Wenlin Zhang, CC BY 4.0. General deficit digit formulas, exact fixed-length maxima, general weighted coefficients, other partition bases, A349553 minimal inputs and general-input unimodality remain open. Existing atlas-lean and Mathlib licenses are retained; no global novelty claim is made.")),
            Node("evenSteps", "Exact source declaration: def evenSteps : ℕ → List ℕ → ℕ | _, [] => 0 | previous, next :: rest => (if previous = 2 * next then 1 else 0) + evenSteps next rest", DescribeRole.Definition),
            Node("digit_one_iff", "Exact source declaration: theorem digit_one_iff (previous next : ℕ) : (previous : ℤ) - 2 * next + 1 = 1 ↔ previous = 2 * next", DescribeRole.Theorem),
            Node("stepDigits", "Exact source declaration: def stepDigits : ℕ → List ℕ → List ℤ | _, [] => [] | previous, next :: rest => ((previous : ℤ) - 2 * next + 1) :: stepDigits next rest", DescribeRole.Definition),
            Node("evenSteps_eq_count", "Exact source declaration: theorem evenSteps_eq_count (previous : ℕ) (parts : List ℕ) : evenSteps previous parts = (stepDigits previous parts).count 1", DescribeRole.Theorem),
            Node("weightedCount", "Exact source declaration: noncomputable def weightedCount {R : Type*} [CommSemiring R] (t : R) (n : ℕ) : R := ∑ p : SourceLists n, t ^ (stepDigits n p.val).count 1", DescribeRole.Definition),
            Node("weightedLengthPolynomial", "Exact source declaration: noncomputable def weightedLengthPolynomial {R : Type*} [CommSemiring R] (t : R) (n : ℕ) : Polynomial R := ∑ p : SourceLists n, Polynomial.C (t ^ (stepDigits n p.val).count 1) * Polynomial.X ^ p.val.length", DescribeRole.Definition),
            Node("codeSource_steps", "Exact source declaration: theorem codeSource_steps (m : ℕ) (hm : 2 ≤ m) (c : DyadicCode m) : evenSteps (2 ^ m + 1) (codeSource m hm c).val = match c with | .inl i => if i = 0 then m - 3 else if i = 1 then m - 2 else m - 1 | .inr r => m - r.val.val - 2 ^ r.val.val - 2", DescribeRole.Theorem),
            Node("weightedLengthPolynomial_dyadic", "Exact source declaration: theorem weightedLengthPolynomial_dyadic {R : Type*} [CommRing R] (t : R) (m : ℕ) (hm : 2 ≤ m) : weightedLengthPolynomial t (2 ^ m + 1) = Polynomial.X ^ m * Polynomial.C (t ^ (m - 3)) + Polynomial.X ^ (m + 1) * Polynomial.C (t ^ (m - 2)) + Polynomial.X ^ (m + 2) * Polynomial.C (t ^ (m - 1)) + ∑ r : Threshold m, Polynomial.X ^ (m - r.val.val) * Polynomial.C (t ^ (m - r.val.val - 2 ^ r.val.val - 2))", DescribeRole.Theorem),
            Node("weightedCount_dyadic", "Exact source declaration: theorem weightedCount_dyadic {R : Type*} [CommRing R] (t : R) (m : ℕ) (hm : 2 ≤ m) : weightedCount t (2 ^ m + 1) = t ^ (m - 3) + t ^ (m - 2) + t ^ (m - 1) + ∑ r : Threshold m, t ^ (m - r.val.val - 2 ^ r.val.val - 2)", DescribeRole.Theorem),
            Node("weightedCount_zero", "Exact source declaration: theorem weightedCount_zero {R : Type*} [CommRing R] (t : R) : weightedCount t 0 = 1", DescribeRole.Theorem),
            Node("weightedCount_one", "Exact source declaration: theorem weightedCount_one {R : Type*} [CommRing R] (n : ℕ) : weightedCount (1 : R) n = (count n : R)", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string statement, DescribeRole role) => Describe.Lean(
        DescribeId.Create("halvingpartitionweights-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(name), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(statement))), role);
}
