using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Partitions;

internal sealed class HalvingPartitionNonregularityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/alekseyev2026halving");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact halving-partition count admits no finite integral family closed under both decimations.",
        H("Halving partitions and unrestricted finite integer families"),
        Blocks(
            Paragraph(Text("The historical integer result remains declared_validated. The full arbitrary-ring audit compiles its realization, variation, sensitivity and dependence proofs, but current source binding is declared_unresolved with IE-C050 source.dictionary_or_proof_coordinate. Newly exposed supplier audits are unfinished. The exact per-target records and missing evidence are listed in https://github.com/the-omega-institute/trureturing/issues/28691 under CLAUDE section 3.9. This audit exception supplies no mathematical proof or independent final acceptance.")),
            Paragraph(Text("Alekseyev's Halving Partitions and Hyperbinary Expansions, "
                + "arXiv:2611.01243v1, Definition 1 and section 6, supplies the source count "
                + "and asks whether it is 2-regular. The source objects here are actual ordered "
                + "lists of positive integers. The virtual predecessor is the total n. "
                + "Every finite length is admitted, repeated entries remain distinct list "
                + "positions, and terminal ones may repeat. At zero the only object is the empty list.")),
            Node("IsHalf", "The two possible values of a half", HalfFormula(),
                "For every previous and next natural value, IsHalf is a disjunction of value "
                + "equalities with the lower and upper integer halves. When previous is even "
                + "the two values coincide; no choice label is stored and no object is doubled.",
                DescribeRole.Definition, true),
            Node("instDecidableIsHalf", "Decidability of the half-value test", HalfDecidableFormula(),
                "For every previous and next natural value, this instance decides IsHalf "
                + "by deciding its disjunction of equalities.", DescribeRole.Definition),
            Node("Follows", "Successive halving along a finite list", FollowsFormula(),
                "The empty list follows any predecessor. A nonempty list follows precisely "
                + "when its first value is a half of the predecessor and its tail follows that "
                + "first value. Positivity and the total are imposed separately. The recursive "
                + "decider tests values and introduces no bound on the list length.", DescribeRole.Definition, true),
            Node("instDecidableFollows", "Decidability of finite-list halving", FollowsDecidableFormula(),
                "For every predecessor and finite natural list, this instance decides Follows "
                + "by recursion on that list, with no length restriction.", DescribeRole.Definition),
            Node("SourceLists", "The independently specified source carrier", SourceFormula(),
                "SourceLists(n) contains exactly the positive lists with sum n satisfying "
                + "Follows(n,p). There is no maximal-chain, sorting, distinctness or final-value "
                + "condition. In particular, positivity and total zero force the empty list.",
                DescribeRole.Definition, true),
            Node("HalvingCompositions", "The finite composition presentation", CompositionFormula(),
                "Mathlib's Composition n stores the same list, positivity and total. Filtering "
                + "it by Follows preserves order and every repeated part. The existing finite "
                + "Composition instance and the decidable filter supply a finite carrier at every n.",
                DescribeRole.Definition),
            Node("sourceEquiv", "List-preserving source correspondence", EquivFormula(),
                "The forward map wraps the original list as a Composition and retains its "
                + "Follows proof. The inverse projects that same list. Both inverse laws are "
                + "proved by the constructors, so no source object is lost or identified. "
                + "The transported Finite instance certifies finiteness of the independent source carrier.",
                DescribeRole.Definition),
            Node("instFintypeHalvingCompositions", "Enumeration of halving compositions", FintypeFormula(),
                "For every natural total n, the instance enumerates the subtype of Composition n "
                + "satisfying Follows, using the decidable predicate.", DescribeRole.Definition),
            Node("instFiniteSourceLists", "Finiteness of the source-list carrier", FiniteFormula(),
                "For every natural total n, the source carrier is finite by transport along "
                + "sourceEquiv(n) from HalvingCompositions(n).", DescribeRole.Definition),
            Node("count", "The exact source count", CountFormula(),
                "The function count(n) is Nat.card of SourceLists(n), defined independently "
                + "of every recurrence and of the dyadic formula used in the proof. The final "
                + "theorem also identifies it with Fintype.card of HalvingCompositions(n) for all n.",
                DescribeRole.Definition, true),
            Node("MatrixFamily", "An unrestricted integral matrix family", MatrixFormula(),
                "The dimension d ranges over every positive natural number. F is any sequence "
                + "of d-dimensional integer vectors and M0,M1 are fixed integral d-by-d matrices. "
                + "Every natural input, including zero, satisfies both displayed vector equalities. "
                + "Coordinate zero is a. No independence, invertibility or dimension cutoff is assumed.",
                DescribeRole.Definition),
            Node("ClosedFamily", "A family indexed by Fin d", FamilyFormula(false),
                "The integer sequences b(i,n) contain a at index zero. Each even and odd "
                + "subsequence is a fixed integer linear combination of the same family. "
                + "The coefficient functions c0 and c1 are independent of n. Equal constituent "
                + "sequences and linear dependence are allowed.", DescribeRole.Definition),
            Node("ArbitraryFamily", "An arbitrary finite indexed family", FamilyFormula(true),
                "The index type I is any finite type, with a distinguished i0 carrying a. "
                + "Here I is the Lean indexing type and hI is its Fintype witness, installed as the local instance. The expression elems(hI) is Fintype.elems, the complete finite enumeration used in both sums. It supplies no basis or algebraic "
                + "independence. Different indices may carry equal sequences. The proof enumerates "
                + "I by Fin(card I) and swaps i0 to zero, transporting both coefficient sums in "
                + "full. Conversely every matrix family supplies such a finite family.",
                DescribeRole.Definition, true),
            Node("claim", "The exact negative matrix event", ClaimFormula(),
                "claim is the negation of MatrixFamily for the integer cast of the independent "
                + "count, on its complete natural domain.", DescribeRole.Definition),
            Node("result", "The whole source question has a negative answer", ResultFormula(),
                "The theorem proves claim, both directions of each family/matrix equivalence "
                + "for every integer sequence a, nonexistence of an arbitrary finite family "
                + "for the source count, and the exact source/composition cardinality identity "
                + "for every n. These are literal finite-family representations; no finite-kernel, "
                + "finite-alphabet, eventual-input or basis substitute enters the statement.",
                DescribeRole.Theorem, acknowledgeSource: true,
                resolution: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("alekseyev-halving-partitions-nonregularity"),
                    ResolutionKind.Refuted)),
            Supplier("powerWord", DescribeRole.Definition),
            Supplier("oddWord", DescribeRole.Definition),
            Supplier("powerWord_length", DescribeRole.Theorem),
            Supplier("oddWord_length", DescribeRole.Theorem),
            Supplier("odd_follows", DescribeRole.Theorem),
            Supplier("powerWord_sum_short", DescribeRole.Theorem),
            Supplier("powerWord_sum_long", DescribeRole.Theorem),
            Supplier("oddWord_sum", DescribeRole.Theorem),
            Supplier("dyadic_source_classification", DescribeRole.Theorem),
            Supplier("oddWord_prefix_injective", DescribeRole.Theorem),
            Supplier("Threshold", DescribeRole.Definition),
            Supplier("DyadicCode", DescribeRole.Definition),
            Supplier("codeParams", DescribeRole.Definition),
            Supplier("code_bounds", DescribeRole.Theorem),
            Supplier("codeSource", DescribeRole.Definition),
            Supplier("codeSource_bijective", DescribeRole.Theorem),
            Supplier("dyadic_source_count", DescribeRole.Theorem),
            Supplier("threshold_mono", DescribeRole.Theorem),
            Supplier("dyadic_plateau", DescribeRole.Theorem),
            Supplier("nonregularity_over", DescribeRole.Theorem),
            Paragraph(Text("For m at least two, every source list at total 2^m+1 has one "
                + "prefix of rounded-up values followed by deterministic powers of two and, "
                + "when the length exceeds m, a tail of ones. If its length l is at most m, "
                + "the number j of rounded-up positions satisfies j=2^(m-l)+1. If l is at least "
                + "m, it satisfies j+(l-m)=2. The exhaustive classification and uniqueness "
                + "produce a bijection with three base lists of lengths m,m+1,m+2 and one "
                + "additional list for each positive r satisfying 2^r+r+1≤m. Thus "
                + "count(2^m+1)=3+#{r≥1:2^r+r+1≤m}. The bound r≤m used in the finite "
                + "code follows from that inequality and restricts no qualifying r.")),
            Paragraph(Text("Between consecutive thresholds the dyadic count is constant. "
                + "Its first difference has 2^r consecutive zero values after the threshold "
                + "2^r+r and is followed by a value one at 2^(r+1)+(r+1). A hypothetical "
                + "matrix family gives the dyadic observations by applying M1 after powers "
                + "of M0. Mathlib's integral Cayley–Hamilton theorem gives a monic forward "
                + "recurrence of order d for them and for their differences. Choose a zero "
                + "block at least that long. Mathlib's recurrence-uniqueness theorem forces "
                + "the whole subsequent tail to be zero, contradicting the next one. "
                + "Only forward propagation is used; the matrices may be singular.")))));

    private static string Exact(string name) => name switch
    {
        "IsHalf" => "Exact source declaration: def IsHalf (previous next : ℕ) : Prop := next = previous / 2 ∨ next = (previous + 1) / 2",
        "Follows" => "Exact source declaration: def Follows : ℕ → List ℕ → Prop | _, [] => True | previous, next :: rest => IsHalf previous next ∧ Follows next rest",
        "SourceLists" => "Exact source declaration: def SourceLists (n : ℕ) := {parts : List ℕ // (∀ x ∈ parts, 0 < x) ∧ parts.sum = n ∧ Follows n parts}",
        "HalvingCompositions" => "Exact source declaration: def HalvingCompositions (n : ℕ) := {c : Composition n // Follows n c.blocks}",
        "sourceEquiv" => "Exact source declaration: def sourceEquiv (n : ℕ) : SourceLists n ≃ HalvingCompositions n where toFun p := ⟨⟨p.1, fun h => p.2.1 _ h, p.2.2.1⟩, p.2.2.2⟩ invFun c := ⟨c.1.blocks, ⟨fun _ h => c.1.blocks_pos h, c.1.blocks_sum, c.2⟩⟩ left_inv p := by cases p; rfl right_inv c := by cases c; rfl",
        "count" => "Exact source declaration: noncomputable def count (n : ℕ) : ℕ := Nat.card (SourceLists n)",
        "MatrixFamily" => "Exact source declaration: def MatrixFamily (a : ℕ → ℤ) : Prop := ∃ d : ℕ, ∃ hd : 0 < d, ∃ F : ℕ → Fin d → ℤ, ∃ M0 M1 : Matrix (Fin d) (Fin d) ℤ, (∀ n, F n ⟨0, hd⟩ = a n) ∧ (∀ n, F (2 * n) = M0.mulVec (F n)) ∧ (∀ n, F (2 * n + 1) = M1.mulVec (F n))",
        "ClosedFamily" => "Exact source declaration: def ClosedFamily (a : ℕ → ℤ) : Prop := ∃ d : ℕ, ∃ hd : 0 < d, ∃ b : Fin d → ℕ → ℤ, ∃ c0 c1 : Fin d → Fin d → ℤ, (∀ n, b ⟨0, hd⟩ n = a n) ∧ (∀ i n, b i (2 * n) = ∑ j, c0 i j * b j n) ∧ (∀ i n, b i (2 * n + 1) = ∑ j, c1 i j * b j n)",
        "claim" => "Exact source declaration: def claim : Prop := ¬ MatrixFamily (fun n => (count n : ℤ))",
        "powerWord" => "Exact source declaration: def powerWord : ℕ → ℕ → List ℕ | _, 0 => [] | 0, l + 1 => 1 :: powerWord 0 l | m + 1, l + 1 => 2 ^ m :: powerWord m l",
        "oddWord" => "Exact source declaration: def oddWord : ℕ → ℕ → ℕ → List ℕ | _, _, 0 => [] | 0, _, l + 1 => 1 :: powerWord 0 l | m + 1, 0, l + 1 => 2 ^ m :: powerWord m l | m + 1, j + 1, l + 1 => (2 ^ m + 1) :: oddWord m j l",
        "powerWord_length" => "Exact source declaration: theorem powerWord_length (m l : ℕ) : (powerWord m l).length = l",
        "oddWord_length" => "Exact source declaration: theorem oddWord_length (m j l : ℕ) : (oddWord m j l).length = l",
        "odd_follows" => "Exact source declaration: theorem odd_follows (m : ℕ) (p : List ℕ) (hp : ∀ x ∈ p, 0 < x) : Follows (2 ^ m + 1) p ↔ ∃ j, j ≤ m ∧ j ≤ p.length ∧ p = oddWord m j p.length",
        "powerWord_sum_short" => "Exact source declaration: theorem powerWord_sum_short (m l : ℕ) (hl : l ≤ m) : (powerWord m l).sum + 2 ^ (m - l) = 2 ^ m",
        "powerWord_sum_long" => "Exact source declaration: theorem powerWord_sum_long (m l : ℕ) (hl : m ≤ l) : (powerWord m l).sum + 1 = 2 ^ m + (l - m)",
        "oddWord_sum" => "Exact source declaration: theorem oddWord_sum (m j l : ℕ) (hjm : j ≤ m) (hjl : j ≤ l) : (oddWord m j l).sum = (powerWord m l).sum + j",
        "dyadic_source_classification" => "Exact source declaration: theorem dyadic_source_classification (m : ℕ) (p : SourceLists (2 ^ m + 1)) : ∃ j, j ≤ m ∧ j ≤ p.1.length ∧ p.1 = oddWord m j p.1.length ∧ (p.1.length ≤ m → j = 2 ^ (m - p.1.length) + 1) ∧ (m ≤ p.1.length → j + (p.1.length - m) = 2)",
        "oddWord_prefix_injective" => "Exact source declaration: theorem oddWord_prefix_injective (m l j k : ℕ) (hjm : j ≤ m) (hjl : j ≤ l) (hkm : k ≤ m) (hkl : k ≤ l) (he : oddWord m j l = oddWord m k l) : j = k",
        "Threshold" => "Exact source declaration: abbrev Threshold (m : ℕ) := {r : Fin (m + 1) // 1 ≤ r.val ∧ 2 ^ r.val + r.val + 1 ≤ m}",
        "DyadicCode" => "Exact source declaration: abbrev DyadicCode (m : ℕ) := Fin 3 ⊕ Threshold m",
        "codeParams" => "Exact source declaration: def codeParams (m : ℕ) : DyadicCode m → ℕ × ℕ | .inl i => if i = 0 then (m, 2) else if i = 1 then (m + 1, 1) else (m + 2, 0) | .inr r => (m - r.1.val, 2 ^ r.1.val + 1)",
        "code_bounds" => "Exact source declaration: theorem code_bounds (m : ℕ) (hm : 2 ≤ m) (c : DyadicCode m) : (codeParams m c).2 ≤ m ∧ (codeParams m c).2 ≤ (codeParams m c).1",
        "codeSource" => "Exact source declaration: def codeSource (m : ℕ) (hm : 2 ≤ m) (c : DyadicCode m) : SourceLists (2 ^ m + 1) := by let l := (codeParams m c).1 let j := (codeParams m c).2 have hb := code_bounds m hm c refine ⟨oddWord m j l, oddWord_positive m j l, code_total m hm c, ?_⟩ apply (odd_follows m _ (oddWord_positive m j l)).mpr refine ⟨j, hb.1, ?_, ?_⟩ · simpa only [oddWord_length] using hb.2 · rw [oddWord_length]",
        "codeSource_bijective" => "Exact source declaration: theorem codeSource_bijective (m : ℕ) (hm : 2 ≤ m) : Function.Bijective (codeSource m hm)",
        "dyadic_source_count" => "Exact source declaration: theorem dyadic_source_count (m : ℕ) (hm : 2 ≤ m) : count (2 ^ m + 1) = 3 + Fintype.card {r : Fin (m + 1) // 1 ≤ r.val ∧ 2 ^ r.val + r.val + 1 ≤ m}",
        "threshold_mono" => "Exact source declaration: theorem threshold_mono {r s : ℕ} (h : r ≤ s) : 2 ^ r + r + 1 ≤ 2 ^ s + s + 1",
        "dyadic_plateau" => "Exact source declaration: theorem dyadic_plateau (m r : ℕ) (hm : 2 ≤ m) (hr : 1 ≤ r) (hlo : 2 ^ r + r + 1 ≤ m) (hhi : m < 2 ^ (r + 1) + (r + 1) + 1) : count (2 ^ m + 1) = 3 + r",
        "nonregularity_over" => "Exact source declaration: theorem nonregularity_over (R : Type*) [CommRing R] [Nontrivial R] : ¬ BinaryDecimation.MatrixFamily (fun n => (count n : R))",
        "ArbitraryFamily" => "Exact source declaration: def ArbitraryFamily (a : ℕ → ℤ) : Prop := ∃ (ι : Type) (hι : Fintype ι), letI : Fintype ι := hι; ∃ (b : ι → ℕ → ℤ) (i0 : ι) (c0 c1 : ι → ι → ℤ), (∀ n, b i0 n = a n) ∧ (∀ i n, b i (2 * n) = ∑ j, c0 i j * b j n) ∧ (∀ i n, b i (2 * n + 1) = ∑ j, c1 i j * b j n)",
        "result" => "Exact source declaration: theorem result : (¬ MatrixFamily (fun n => (count n : ℤ))) ∧ (∀ a : ℕ → ℤ, ClosedFamily a ↔ MatrixFamily a) ∧ (∀ a : ℕ → ℤ, ArbitraryFamily a ↔ MatrixFamily a) ∧ (¬ ArbitraryFamily (fun n => (count n : ℤ))) ∧ (∀ n, count n = Fintype.card (HalvingCompositions n)) ∧ count 0 = 1",
        _ => name
    };

    private static DocumentBlock Supplier(string name, DescribeRole role) => Describe.Lean(
        DescribeId.Create("halving-source-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(name), StatementSource.WithoutFormula(),
        name is "dyadic_source_classification" or "dyadic_source_count"
            ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(
            name == "nonregularity_over"
                ? "The actual count has no fixed binary matrix representation over every nonzero commutative unital ring, including positive characteristic and zero divisors."
                : "The original-place source supplier is shared by the actual length and weighted proofs. The list, order, sum constraint and original quantifiers are preserved.")), Paragraph(Text(Exact(name)))), role);

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, bool literature = false, bool acknowledgeSource = false,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("halving-partitions-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source)
                : acknowledgeSource ? AssessedProvenance.FromRepo(Source) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula HalfFormula() => Disp(All("p", N(), All("q", N(),
        IffF(Call("IsHalf", F.Id("p"), F.Id("q")), OrF(
            Eq(F.Id("q"), Call("natDiv", F.Id("p"), D(2))),
            Eq(F.Id("q"), Call("natDiv", Add(F.Id("p"), D(1)), D(2))))))));

    private static Formula FollowsFormula() => Disp(AndF(
        All("p", N(), Call("Follows", F.Id("p"), Call("nil"))),
        All("p", N(), All("q", N(), All("t", ListN(),
            IffF(Call("Follows", F.Id("p"), Call("cons", F.Id("q"), F.Id("t"))),
                AndF(Call("IsHalf", F.Id("p"), F.Id("q")), Call("Follows", F.Id("q"), F.Id("t")))))))));

    private static Formula HalfDecidableFormula() => Disp(Seq(F.Id("instDecidableIsHalf"), Colon, Sp,
        All("previous", N(), All("next", N(),
            Call("Decidable", Call("IsHalf", F.Id("previous"), F.Id("next")))))));

    private static Formula FollowsDecidableFormula() => Disp(Seq(F.Id("instDecidableFollows"), Colon, Sp,
        All("previous", N(), All("parts", ListN(),
            Call("Decidable", Call("Follows", F.Id("previous"), F.Id("parts")))))));

    private static Formula FintypeFormula() => Disp(Seq(F.Id("instFintypeHalvingCompositions"), Colon, Sp,
        All("n", N(), Call("Fintype", Call("HalvingCompositions", F.Id("n"))))));

    private static Formula FiniteFormula() => Disp(Seq(F.Id("instFiniteSourceLists"), Colon, Sp,
        All("n", N(), Call("Finite", Call("SourceLists", F.Id("n"))))));

    private static Formula SourceFormula() => Disp(All("n", N(),
        Eq(Call("SourceLists", F.Id("n")), Seq(OpenBrace, F.Id("p"), Colon, Sp, ListN(), Sp, Mid, Sp,
            AndF(All("x", N(), ImpliesF(Member(F.Id("x"), F.Id("p")), Lt(D(0), F.Id("x")))),
                AndF(Eq(Call("sum", F.Id("p")), F.Id("n")), Call("Follows", F.Id("n"), F.Id("p")))), CloseBrace))));

    private static Formula CompositionFormula() => Disp(All("n", N(),
        Eq(Call("HalvingCompositions", F.Id("n")), Seq(OpenBrace, F.Id("c"), Colon, Sp,
            Call("Composition", F.Id("n")), Sp, Mid, Sp,
            Call("Follows", F.Id("n"), Call("blocks", F.Id("c"))), CloseBrace))));

    private static Formula EquivFormula() => Disp(All("n", N(),
        Seq(Call("sourceEquiv", F.Id("n")), Colon, Sp, Call("SourceLists", F.Id("n")), Sp,
            F.Equiv, Sp, Call("HalvingCompositions", F.Id("n")))));

    private static Formula CountFormula() => Disp(All("n", N(),
        Eq(Call("count", F.Id("n")), Call("card", Call("SourceLists", F.Id("n"))))));

    private static Formula MatrixFormula()
    {
        var d = F.Id("d"); var n = F.Id("n"); var a = F.Id("a");
        var vectors = Arrow(Call("Fin", d), Z());
        var matrices = Arrow(Call("Fin", d), Arrow(Call("Fin", d), Z()));
        var first = All("n", N(), Eq(Call("F", n, D(0)), Call("a", n)));
        var even = All("n", N(), Eq(Call("F", Mul(D(2), n)),
            Call("mulVec", F.Id("M0"), Call("F", n))));
        var odd = All("n", N(), Eq(Call("F", Add(Mul(D(2), n), D(1))),
            Call("mulVec", F.Id("M1"), Call("F", n))));
        return Disp(All("a", SequenceType(), IffF(Call("MatrixFamily", a),
            Some("d", N(), AndF(Lt(D(0), d), Some("F", Arrow(N(), vectors),
                Some("M0", matrices, Some("M1", matrices, AndF(first, AndF(even, odd))))))))));
    }

    private static Formula FamilyFormula(bool arbitrary)
    {
        var index = arbitrary ? F.Id("I") : Call("Fin", F.Id("d"));
        var i0 = arbitrary ? F.Id("i0") : D(0);
        var i = F.Id("i"); var j = F.Id("j"); var n = F.Id("n");
        Formula Row(string c, Formula input) => All("i", index, All("n", N(),
            Eq(Call("b", i, input), Seq(new Formula.Subscript(Sum, arbitrary
                ? Member(j, Call("elems", F.Id("hI"))) : Seq(j, Colon, Sp, index)),
                Mul(Call(c, i, j), Call("b", j, n))))));
        var law = AndF(All("n", N(), Eq(Call("b", i0, n), Call("a", n))),
            AndF(Row("c0", Mul(D(2), n)), Row("c1", Add(Mul(D(2), n), D(1)))));
        var coefficients = Some("c0", Arrow(index, Arrow(index, Z())),
            Some("c1", Arrow(index, Arrow(index, Z())), law));
        var body = Some("b", Arrow(index, SequenceType()),
            arbitrary ? Some("i0", index, coefficients) : coefficients);
        var exists = arbitrary
            ? Some("I", new Formula.NamedConstant(FormulaIdentifier.Create("Type")),
                Some("hI", Call("Fintype", index), body))
            : Some("d", N(), AndF(Lt(D(0), F.Id("d")), body));
        return Disp(All("a", SequenceType(), IffF(Call(arbitrary ? "ArbitraryFamily" : "ClosedFamily", F.Id("a")), exists)));
    }

    private static Formula CastCount() => Parenthesized(Seq(F.Id("n"), Colon, Sp, N(), Sp, Mapsto, Sp,
        Call("Int", Call("count", F.Id("n")))));
    private static Formula ClaimFormula() => Disp(IffF(F.Id("claim"),
        new Formula.Not(Call("MatrixFamily", CastCount()))));
    private static Formula ResultFormula() => Disp(AndF(F.Id("claim"), AndF(
        All("a", SequenceType(), IffF(Call("ClosedFamily", F.Id("a")), Call("MatrixFamily", F.Id("a")))),
        AndF(All("a", SequenceType(), IffF(Call("ArbitraryFamily", F.Id("a")), Call("MatrixFamily", F.Id("a")))),
            AndF(new Formula.Not(Call("ArbitraryFamily", CastCount())),
                AndF(All("n", N(), Eq(Call("count", F.Id("n")), Call("card", Call("HalvingCompositions", F.Id("n"))))), Eq(Call("count", D(0)), D(1))))))));

    private static Formula N() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Z() => new Formula.Integers();
    private static Formula ListN() => Call("List", N());
    private static Formula SequenceType() => Arrow(N(), Z());
    private static Formula Arrow(Formula a, Formula b) => Parenthesized(Seq(a, Sp, To, Sp, b));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula AndF(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula OrF(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula IffF(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula ImpliesF(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string v, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), type, body);
    private static Formula Some(string v, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(v), type, body);
}
