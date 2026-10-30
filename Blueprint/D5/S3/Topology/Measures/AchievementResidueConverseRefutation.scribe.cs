using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Measures;

internal sealed class AchievementResidueConverseRefutationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/Measures/AchievementResidueConverseRefutation.";
    private const string FullClaim =
        "∀ (m : ℕ) (hm : 0 < m) (k : Fin m → ℕ) (n : ℕ), "
        + "(∀ i, 0 < k i) → Antitone k → 1 < n → (blockSums k).card = n → "
        + "(∀ i, ¬ n ∣ k i) → 0 < volume (achievement hm k n) → "
        + "(blockSums k).image (fun s => s % n) = Finset.range n";

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Fin => Call("Fin", V("m"));
    private static Formula Coeff => Seq(Fin, Sp, To, Sp, Nat);
    private static Formula Pos => Seq(D(0), Sp, Lt, Sp, V("m"));
    private static Formula Bound(string name, Formula type) =>
        Seq(Open, V(name), Sp, Colon, Sp, type, Close);
    private static Formula All(string name, Formula type) =>
        Seq(Forall, Sp, Bound(name, type), Comma, Sp);
    private static Formula Par(Formula body) => Seq(Open, body, Close);
    private static Formula Arr => Seq(Sp, Rightarrow, Sp);
    private static Formula Eqn(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula BlocksOfK => Call("blockSums", V("k"));
    private static Formula AchievementOfK => Call("achievement", V("hm"), V("k"), V("n"));
    private static Formula Residues => Call("image",
        Seq(Bound("s", Nat), Sp, Mapsto, Sp, Call("mod", V("s"), V("n"))), BlocksOfK);

    private static Formula ClaimBody() => new Formula.Aligned([
        Seq(All("m", Nat), All("hm", Pos), All("k", Coeff), All("n", Nat)),
        Seq(Par(Seq(All("i", Fin), D(0), Sp, Lt, Sp, Call("k", V("i")))), Arr,
            Call("Antitone", V("k")), Arr, D(1), Sp, Lt, Sp, V("n"), Arr),
        Seq(Eqn(Call("card", BlocksOfK), V("n")), Arr),
        Seq(Par(Seq(All("i", Fin), Neg, Sp,
            Par(Seq(V("n"), Sp, Mid, Sp, Call("k", V("i")))))), Arr),
        Seq(D(0), Sp, Lt, Sp, Call("volume", AchievementOfK), Arr),
        Eqn(Residues, Call("range", V("n")))
    ]);

    private static Formula BlockSumsStatement() => Disp(new Formula.Aligned([
        Seq(All("m", Nat), All("k", Coeff)),
        Eqn(BlocksOfK, Call("image",
            Seq(Bound("b", Seq(Fin, Sp, To, Sp, V("Bool"))), Sp, Mapsto, Sp,
                Sum, Underscore, Grp(Seq(V("i"), Colon, Sp, Fin)), Sp,
                Call("ite", Call("b", V("i")), Call("k", V("i")), D(0))),
            Call("univ", Seq(Fin, Sp, To, Sp, V("Bool")))))
    ]));

    private static Formula SourceTermStatement() => Disp(new Formula.Aligned([
        Seq(All("m", Nat), All("hm", Pos), All("k", Coeff), All("n", Nat), All("t", Nat)),
        Eqn(Call("sourceTerm", V("hm"), V("k"), V("n"), V("t")),
            Seq(Frac,
                Grp(Call("realCast", Call("k", Seq(Langle,
                    Call("mod", V("t"), V("m")), Comma, Sp,
                    Call("modLt", V("t"), V("hm")), Rangle)))),
                Grp(Seq(Par(Call("realCast", V("n"))), Caret,
                    Grp(Seq(Call("natDiv", V("t"), V("m")), Plus, D(1)))))))
    ]));

    private static Formula AchievementStatement() => Disp(new Formula.Aligned([
        Seq(All("m", Nat), All("hm", Pos), All("k", Coeff), All("n", Nat)),
        Eqn(AchievementOfK, Seq(OpenBrace, Sp, V("x"), Colon, Sp, Real, Sp, Mid, Sp,
            Exists, Sp, Bound("A", Call("Set", Nat)), Comma, Sp,
            Call("HasSum", Seq(Bound("t", V("A")), Sp, Mapsto, Sp,
                Call("sourceTerm", V("hm"), V("k"), V("n"), Call("val", V("t")))), V("x")),
            Sp, CloseBrace))
    ]));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Indexed infinite achievement sets refute the unnormalized residue converse.",
        H("Indexed multigeometric achievement sets and residues"),
        Blocks(
            Paragraph(Text(
                "The question concerns positive weakly decreasing indexed natural coefficients, with repeated positions independently selectable. "
                + "Its two source locations are Section 2, Problem 9 of Achievement sets — current results and open problems, "
                + "and Section 5.1, Problem 1 of Kenyon theorem revisited. They state one question. "
                + "The original coefficients are retained, without division by their greatest common divisor.")),
            Describe.Lean(DescribeId.Create("block-sums"), DeclarationHandle.Create(Owner + "blockSums"),
                H("Distinct indexed Boolean block sums"), StatementSource.FromAuthor(BlockSumsStatement()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Topology/glabpruswisniowski2025achievement")),
                Blocks(Paragraph(Text(
                    "For every implicit m : ℕ and k : Fin m → ℕ, blockSums k : Finset ℕ is "
                    + "Finset.univ.image (fun b : Fin m → Bool => ∑ i, if b i then k i else 0). "
                    + "The universal finite set ranges over every Boolean function on Fin m, including when m = 0. "
                    + "ite is the Boolean if-then-else operation. Only equal sum values are identified; equal coefficients at distinct indices remain independent choices."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("source-term"), DeclarationHandle.Create(Owner + "sourceTerm"),
                H("The original infinite source sequence"), StatementSource.FromAuthor(SourceTermStatement()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Topology/glabpruswisniowski2025achievement")),
                Blocks(Paragraph(Text(
                    "For every implicit m : ℕ, hm : 0 < m, k : Fin m → ℕ and n t : ℕ, sourceTerm hm k n t : ℝ equals "
                    + "(k ⟨t % m, Nat.mod_lt t hm⟩ : ℝ) / (n : ℝ) ^ (t / m + 1). "
                    + "Here mod is natural remainder, natDiv is natural quotient, modLt is the proof Nat.mod_lt, and realCast is coercion to ℝ. "
                    + "Thus t = jm + i selects the original position i in block j, and the first denominator exponent is one. "
                    + "The definition itself imposes no positivity, ordering or n > 1 hypothesis; these enter claim."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("achievement"), DeclarationHandle.Create(Owner + "achievement"),
                H("Genuine convergent subseries"), StatementSource.FromAuthor(AchievementStatement()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Topology/glabkula2025kenyon")),
                Blocks(Paragraph(Text(
                    "For every implicit m : ℕ, hm : 0 < m, k : Fin m → ℕ and n : ℕ, achievement hm k n : Set ℝ is exactly "
                    + "{x | ∃ A : Set ℕ, HasSum (fun t : A => sourceTerm hm k n t.val) x}. "
                    + "The binder t : A ranges over the subtype of original indices lying in A. HasSum is the actual infinite-series convergence relation. "
                    + "A may be any subset, including the empty set or an infinite set; no finite approximation or interval is part of the definition."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("claim"), DeclarationHandle.Create(Owner + "claim"),
                H("The full unnormalized residue implication"),
                StatementSource.FromAuthor(Disp(Seq(V("claim"), Sp, Leftrightarrow, Sp, ClaimBody()))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Topology/glabpruswisniowski2025achievement")),
                Blocks(Paragraph(Text("The closed definition claim : Prop has the exact body: " + FullClaim + ".")),
                    Paragraph(Text(
                        "All indices i range over Fin m. Antitone means weakly decreasing in this index order, not strictly decreasing. "
                        + "card counts distinct block-sum values, volume is Lebesgue measure on ℝ, and image and range are the finite-set operations. "
                        + "There is no coprimality, primitive-coefficient, normalization or distinct-coefficient assumption."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Owner + "result"),
                H("Negation of the full residue implication"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Sp, Par(ClaimBody())))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Topology/glabpruswisniowski2025achievement")),
                Blocks(Paragraph(Text(
                        "The theorem is result : ¬ claim, with no free parameters or hypotheses. The proposition negated has the exact body: " + FullClaim + ".")),
                    Paragraph(Text(
                        "Take m = 3, k = (9, 3, 3) and n = 6. The distinct block sums are {0, 3, 6, 9, 12, 15}, "
                        + "so their cardinality is six and their residues modulo six are {0, 3}; residue one is missing. "
                        + "The coefficients are positive and weakly decreasing, and none is divisible by six.")),
                    Paragraph(Text(
                        "For each subset A of the original indices, Nat.divModEquiv 3 regroups its genuinely summable subseries into blocks. "
                        + "Each Boolean block has value 3d for a digit d ∈ Fin 6. The resulting HasSum equals 3 * Real.ofDigits (selectedDigits A). "
                        + "Conversely, digitBits selects the two repeated coefficient positions independently and realizes every base-six digit. "
                        + "Applying this selection at every block realizes every digit sequence as a subset of the original indices. "
                        + "Real.ofDigits_SurjOn and Real.ofDigits_le_one therefore give achievement (by decide : 0 < 3) coefficients 6 = Set.Icc 0 3 in both directions, including endpoints. "
                        + "Real.volume_Icc supplies positive Lebesgue measure, contradicting the full residue conclusion.")),
                    Paragraph(Text(
                        "The source sequence starts with denominator exponent one. The interval endpoint printed in the surrounding Nitecki theorem has a different scale; "
                        + "the argument here uses the actual HasSum equality instead of that endpoint. "
                        + "The tuple has a common factor three. Dividing it out changes residues modulo six and changes the assertion. "
                        + "Statements requiring primitive or normalized coefficients are separate questions and are not established here."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("glab-2025-achievement-residue-converse"),
                    ResolutionKind.Refuted)))));
}
