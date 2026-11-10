using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Partitions;

internal sealed class HalvingPartitionWeightsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Partitions/HalvingPartitionWeights.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/mazhang2026weightedhalving");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "HalvingPartitionWeights",
        H("HalvingPartitionWeights"),
        Blocks(
            Paragraph(Text("These results preserve the actual SourceLists count, including repeated terminal ones and the unique empty list at zero. The dyadic enumeration specializes Alekseyev (2026), Theorem 5. The ring, weighted, representation-base and statistical scope follows the written note by Haobo Ma then Wenlin Zhang (7 November 2026, CC BY 4.0). No global novelty or independent final acceptance is asserted.")),
            Node("evenSteps", "Counts precisely the positions where the manuscript digit p-2q+1 equals one. The equality p=2q is expressed in naturals without truncated subtraction.", DescribeRole.Definition),
            Node("digit_one_iff", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Theorem),
            Node("stepDigits", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Definition),
            Node("evenSteps_eq_count", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Theorem),
            Node("weightedCount", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Definition),
            Node("weightedLengthPolynomial", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Definition),
            Node("codeSource_steps", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Theorem),
            Node("weightedLengthPolynomial_dyadic", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Theorem),
            Node("weightedCount_dyadic", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Theorem),
            Node("weightedCount_zero", "The compiler-derived statement fixes the complete parameters and hypotheses.", DescribeRole.Theorem))));

    private static string Exact(string name) => name switch
    {
        "evenSteps" => "Exact source statement: def evenSteps : ℕ → List ℕ → ℕ | _, [] => 0 | previous, next :: rest => (if previous = 2 * next then 1 else 0) + evenSteps next rest /-- Exact identification with the manuscript's integer digit, on every step. -/ theorem digit_one_iff (previous next : ℕ) : (previous : ℤ) - 2 * next + 1 = 1 ↔ previous = 2 * next",
        "digit_one_iff" => "Exact source statement: theorem digit_one_iff (previous next : ℕ) : (previous : ℤ) - 2 * next + 1 = 1 ↔ previous = 2 * next",
        "stepDigits" => "Exact source statement: def stepDigits : ℕ → List ℕ → List ℤ | _, [] => [] | previous, next :: rest => ((previous : ℤ) - 2 * next + 1) :: stepDigits next rest /-- The recursively counted exponent equals the literal number of digit ones. -/ theorem evenSteps_eq_count (previous : ℕ) (parts : List ℕ) : evenSteps previous parts = (stepDigits previous parts).count 1",
        "evenSteps_eq_count" => "Exact source statement: theorem evenSteps_eq_count (previous : ℕ) (parts : List ℕ) : evenSteps previous parts = (stepDigits previous parts).count 1",
        "weightedCount" => "Exact source statement: noncomputable def weightedCount {R : Type*} [CommSemiring R] (t : R) (n : ℕ) : R := ∑ p : SourceLists n, t ^ (stepDigits n p.val).count 1",
        "weightedLengthPolynomial" => "Exact source statement: noncomputable def weightedLengthPolynomial {R : Type*} [CommSemiring R] (t : R) (n : ℕ) : Polynomial R := ∑ p : SourceLists n, Polynomial.C (t ^ (stepDigits n p.val).count 1) * Polynomial.X ^ p.val.length",
        "codeSource_steps" => "Exact source statement: theorem codeSource_steps (m : ℕ) (hm : 2 ≤ m) (c : DyadicCode m) : evenSteps (2 ^ m + 1) (codeSource m hm c).val = match c with | .inl i => if i = 0 then m - 3 else if i = 1 then m - 2 else m - 1 | .inr r => m - r.val.val - 2 ^ r.val.val - 2",
        "weightedLengthPolynomial_dyadic" => "Exact source statement: theorem weightedLengthPolynomial_dyadic {R : Type*} [CommRing R] (t : R) (m : ℕ) (hm : 2 ≤ m) : weightedLengthPolynomial t (2 ^ m + 1) = Polynomial.X ^ m * Polynomial.C (t ^ (m - 3)) + Polynomial.X ^ (m + 1) * Polynomial.C (t ^ (m - 2)) + Polynomial.X ^ (m + 2) * Polynomial.C (t ^ (m - 1)) + ∑ r : Threshold m, Polynomial.X ^ (m - r.val.val) * Polynomial.C (t ^ (m - r.val.val - 2 ^ r.val.val - 2))",
        "weightedCount_dyadic" => "Exact source statement: theorem weightedCount_dyadic {R : Type*} [CommRing R] (t : R) (m : ℕ) (hm : 2 ≤ m) : weightedCount t (2 ^ m + 1) = t ^ (m - 3) + t ^ (m - 2) + t ^ (m - 1) + ∑ r : Threshold m, t ^ (m - r.val.val - 2 ^ r.val.val - 2)",
        "weightedCount_zero" => "Exact source statement: theorem weightedCount_zero {R : Type*} [CommRing R] (t : R) : weightedCount t 0 = 1",
        _ => name
    };

    private static DocumentBlock Node(string name, string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create("halvingpartitionweights-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(name), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose)), Paragraph(Text(Exact(name)))), role);
}
