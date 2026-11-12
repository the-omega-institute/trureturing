using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class CoonsAdjacentGrowthRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/CoonsAdjacentGrowthRefutation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual bounded-digit radix-four counts with bounds five and six both have "
            + "upper logarithmic growth exponent one half.",
        H("Equal adjacent growth exponents in Coons's partition question"),
        Blocks(
            Paragraph(Text(
                "Source: Michael Coons, arXiv:2611.08109v1, Section 3, final strict "
                + "adjacent-multiplicity logarithmic limsup question, with the count "
                + "defined by the product in Section 2. The source is licensed CC BY 4.0. "
                + "The question quantifies over every natural radix ell at least two "
                + "and every natural k at least ell minus one, including ell=2,k=1. "
                + "It asks for strict growth from k to k+1 at the same radix. "
                + "The introductory index typo is resolved by the Section 2 product. "
                + "The separate liminf and first-linear-threshold questions are outside this statement. "
                + "The source attribution identifies the question and its count convention; "
                + "it does not establish historical priority for the counterexample.")),
            Node("weight", "Source weighted value", "weight",
                "For ell in the natural numbers and a : Nat →₀ Nat, weight ell a is "
                + "the sum over support(a) of a(i) times ell^i. All terms are natural numbers. "
                + "The support is intrinsic to the function, so zero padding has no identity.",
                DescribeRole.Definition),
            Node("partitions", "Actual finite-support source carrier", "Partitions",
                "Partitions k ell n is exactly the subtype of finitely supported "
                + "Nat-valued functions a with a(i) at most k for every natural i "
                + "and weight ell a=n. Each function occurs once. No word length "
                + "or selected subsequence enters this definition.", DescribeRole.Definition),
            Node("count", "Finite cardinality", "count",
                "count k ell n is Nat.card (Partitions k ell n). Finiteness is proved "
                + "for every k,n and every ell at least two. The private count_zero lemma "
                + "proves count k ell 0=1: positivity of every power forces all coefficients "
                + "of a zero-weight function to vanish. That lemma is consumed by count_positive.",
                DescribeRole.Definition),
            Node("readout", "Natural-input logarithmic readout", "readout",
                "readout k ell n is Real.log (count k ell n) / Real.log n. "
                + "At n=0,1 this uses Mathlib's total real logarithm and division conventions. "
                + "Every tail starts at least at two; positivity of the count and of log n "
                + "is proved wherever the asymptotic estimates use division.", DescribeRole.Definition),
            Node("exponent", "Extended-real every-tail limsup", "exponent",
                "exponent k ell is the infimum, over natural N with 2≤N, of the supremum, "
                + "over every natural n with N≤n, of the real readout embedded in EReal. "
                + "This is the ordinary extended-real tail definition itself. There is no "
                + "real-limsup boundedness premise and no replacement by block maxima.", DescribeRole.Definition),
            Node("claim", "The complete universal event", "claim",
                "claim : Prop is ∀ ell : Nat, 2≤ell → ∀ k : Nat, ell-1≤k → "
                + "exponent k ell < exponent (k+1) ell. It has no finiteness conjunct, "
                + "extra parameter hypothesis or excluded endpoint.", DescribeRole.Definition),
            Node("finite", "Support restriction proves actual finiteness", "partitions_finite",
                "For every k ell n and hell : 2≤ell, Finite (Partitions k ell n). "
                + "If n<ell^L, any nonzero coefficient at i≥L contributes at least ell^L, "
                + "a contradiction. Restriction to Fin L is injective into Fin L → Fin(k+1). "
                + "One can take L=n+1. The pack and weight_window "
                + "bridges prove that extension by zeros has exactly the original support sum.", DescribeRole.Theorem),
            Node("positive", "Ordinary radix representations are admitted", "count_positive",
                "For every k ell n with 2≤ell and ell-1≤k, 0<count k ell n. "
                + "The digits Nat.digits ell n lie below ell, and Nat.ofDigits_digits "
                + "gives their weighted value n. Extension by zeros yields an actual "
                + "finite-support member. At zero the unique zero function gives count one.", DescribeRole.Theorem),
            Node("upper", "The uniform bound at every natural input", "count_upper",
                "For every natural k,m,n, k≤6 and n<4^(m+1) imply count k 4 n≤2^m. "
                + "Map a partition to the m quotients a(i)/4 for i<m. Each quotient is "
                + "zero or one, and the top quotient is zero because n<4^(m+1). "
                + "Equal weighted sums determine equal units digits modulo four; equality "
                + "of the quotients then determines equal full digits. Induction after "
                + "removing the equal head proves injectivity. The finite cardinality "
                + "bound is thus for actual functions. Taking m=Nat.log 4 n proves "
                + "count(k,4,n)^2≤n for every n≥1, without a recurrence surrogate.", DescribeRole.Theorem),
            Node("repunit", "The unbounded lower family", "repunit",
                "repunit m is the sum of 4^i for 0≤i<m+1. Its bounds are "
                + "4^m≤repunit m<4^(m+1). The index m counts interior binary carries; "
                + "the repunit has m+1 digits.", DescribeRole.Definition),
            Node("repunit-count", "Distinct carries attain the count bound", "count_repunit",
                "For every k,m with 5≤k≤6, count k 4 (repunit m)=2^m. "
                + "An arbitrary v : Fin m → Fin 2 supplies carries c(1),...,c(m), "
                + "with c(0)=c(m+1)=0. Set a(i)=1+4c(i+1)-c(i) for i<m+1, "
                + "and zero elsewhere. These natural digits lie in {0,1,4,5}. "
                + "The balance a(i)+c(i)=1+4c(i+1), multiplied by 4^i and summed, "
                + "telescopes to the repunit value. Equality of the functions recursively "
                + "recovers all carries from c(0)=0, including a top digit equal to zero. "
                + "The injection gives 2^m distinct partitions, and count_upper gives equality.", DescribeRole.Theorem),
            Node("tail", "Every entire natural tail has supremum one half", "tail_supremum",
                "For all k,N with 5≤k≤6 and 2≤N, the EReal supremum of readout(k,4,n) "
                + "over all natural n≥N equals the real number 1/2 embedded in EReal. "
                + "The square bound and positive logarithms give 0≤readout≤1/2 for every n≥2. "
                + "At repunit m, count=2^m and log(repunit m)≤(m+1)log 4, hence "
                + "readout≥m/(2(m+1)). Given any real r<1/2 and any N≥2, "
                + "choose natural m larger than both N and 2r/(1-2r). Then repunit m≥N "
                + "and r<m/(2(m+1)). Density of real numbers in EReal proves the "
                + "lower bound for that whole tail supremum, including the infinite "
                + "endpoint possibilities. This proves finiteness rather than assuming it.", DescribeRole.Theorem),
            Node("half", "Both adjacent exponents", "exponent_eq_half",
                "For every natural k with 5≤k≤6, exponent k 4=(1/2 : Real), "
                + "embedded in EReal. Every tail supremum equals that value, so its "
                + "infimum does too; the set of permitted tails contains N=2.", DescribeRole.Theorem),
            Node("result", "Literal refutation of the complete event", "result",
                "The theorem has literal type Not claim. Instantiate its putative "
                + "universal strict inequality at ell=4,k=5, an admissible pair. "
                + "The two exact exponents for k=5 and k+1=6 are both one half, "
                + "contradicting strictness. The conclusion concerns the entire original "
                + "universal event and uses the same radix on both sides.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("coons-adjacent-growth-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
