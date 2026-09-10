using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns;

internal sealed class DerangementRatioNonconvergenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Patterns/DerangementRatioNonconvergence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/vatter2026assortment");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Av(12) has one permutation per length and a nonconvergent derangement ratio.",
        H("A Literal Negative Answer to Vatter's Question 4.3"),
        Blocks(
            Paragraph(Text(
                "Question 4.3 of Vincent Vatter's arXiv:2602.16355v2 asks whether the "
                + "derangement ratio converges for every permutation class. This is a literal "
                + "counterexample to the question as stated; the author may have had nontrivial "
                + "(e.g. infinite-growth) classes in mind. The module claims only the refutation "
                + "of the universally quantified statement. The literature provenance on the "
                + "two answer nodes identifies the question, not a published negative answer; "
                + "the counterexample and its proof are derived here.")),
            Paragraph(Text(
                "Perm(n) denotes Equiv.Perm(Fin(n)), with positions numbered from zero. "
                + "OrderEmbedding denotes an order embedding of positions. The record field "
                + "mem is the length-indexed family; downset is its displayed closure law. "
                + "rev(n) denotes Mathlib's Fin.revPerm, sending i to n-1-i. Every cardinality "
                + "is Fintype.card. The quotient defining ratio is real division after casting "
                + "both natural cardinalities to the reals. Length zero is included.")),
            Node("Contains", "Pattern containment", ContainsFormula(),
                "An order embedding selects positions and preserves the relative order of "
                + "the selected values in both directions.", DescribeRole.Definition),
            Node("PermClass", "Permutation classes as downsets", ClassFormula(),
                "This record has exactly the family mem and the proof field downset. "
                + "The displayed record description gives the full type of both fields.",
                DescribeRole.Definition),
            Node("IsDerangement", "Fixed-point-free permutations", DerangementFormula(),
                "This is membership in Mathlib's derangements set, whose definition is "
                + "the displayed universal inequality.", DescribeRole.Definition),
            Node("Av12", "The decreasing permutation class", Av12Formula(),
                "A pattern of a decreasing permutation is decreasing: the position embedding "
                + "takes i<j to f(i)<f(j), and the value-order equivalence transfers the "
                + "reversed inequality back to the pattern. This supplies the downset field. "
                + "Strict decrease is exactly avoidance of the increasing pattern 12.",
                DescribeRole.Definition),
            Node("av12_mem_iff", "The unique member at every length", MembershipFormula(),
                "Composing a decreasing permutation with Fin.rev is strictly increasing. "
                + "Mathlib's StrictMono.apply_eq on a finite linear order makes that composition "
                + "the identity; applying reversal again identifies the permutation."),
            Node("rev_fixed_iff", "The middle-position criterion", FixedFormula(),
                "The equality of Fin values is n-(i.val+1)=i.val. The bound i.val<n "
                + "turns this into 2*i.val+1=n, with natural subtraction."),
            Node("rev_isDerangement_iff", "Parity decides derangements", ParityFormula(),
                "At odd length the proof constructs the position with value n div 2, "
                + "proves it is in Fin(n), and uses the middle-position criterion to exhibit "
                + "a fixed point. At even length that criterion is impossible. The empty "
                + "permutation is a derangement by vacuity."),
            Node("card_av12", "One member at every length", CardFormula(),
                "The membership characterization identifies each length slice with the "
                + "singleton containing reversal."),
            Node("card_derangements_av12", "Count of derangements", DerangementCardFormula(),
                "The underlying length slice is a subsingleton. At even length the proof "
                + "constructs its derangement member; at odd length any alleged member "
                + "contradicts the parity criterion."),
            Node("ratio", "The derangement ratio", RatioDefinitionFormula(),
                "The numerator counts the subtype of members that are derangements. "
                + "The denominator counts the entire length slice. Real division is total; "
                + "for Av(12) the denominator is always one.", DescribeRole.Definition),
            Node("ratio_av12", "The alternating ratio", RatioFormula(),
                "Substituting both cardinalities gives one at even length and zero at odd "
                + "length. Thus the positive-length sequence begins 0,1,0,1."),
            Node("vatter_question_4_3_answer_no", "Av(12) has no ratio limit",
                Disp(NoLimit(Av())),
                "Both index maps k to 2*k and k to 2*k+1 tend to atTop. The corresponding "
                + "ratio subsequences are constantly one and zero. Uniqueness of real limits "
                + "would force a putative common limit to equal both, a contradiction.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("vatter-question-4-3-derangement-ratio"),
                    ResolutionKind.Refuted)),
            Node("exists_permClass_ratio_not_convergent", "The universal question is false",
                Disp(Seq(Exists, Sp, C(), Colon, Sp, Named("PermClass"), Comma, Sp,
                    NoLimit(C()))),
                "Choose the downset Av(12). This refutes the question with no additional "
                + "growth assumption; it makes no claim about restricted variants.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role = DescribeRole.Theorem,
        AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("derangement-ratio-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula N() => F.Id("n");
    private static Formula K() => F.Id("k");
    private static Formula C() => F.Id("C");
    private static Formula Av() => Named("Av12");
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula formula) => Seq(Open, formula, Close);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);
    private static Formula Fin(Formula length) => Call("Fin", length);
    private static Formula Perm(Formula length) => Call("Perm", length);
    private static Formula Rev(Formula length) => Call("rev", length);
    private static Formula Mem(Formula family, Formula length) => Call("mem", family, length);
    private static Formula Ratio(Formula family, Formula length) => Call("ratio", family, length);
    private static Formula Member(Formula value, Formula set) => Seq(value, Sp, InMacro, Sp, set);
    private static Formula Cardinality(Formula type) => Call("card", type);
    private static Formula Bound(Formula variable, Formula type) =>
        Seq(Forall, Sp, variable, Colon, Sp, type, Comma, Sp);
    private static Formula BoundPair(Formula first, Formula second, Formula type) =>
        Seq(Forall, Sp, first, Comma, Sp, second, Colon, Sp, type, Comma, Sp);
    private static Formula ParityValue() => Seq(Named("if"), Sp, Call("Even", N()), Sp,
        Named("then"), Sp, D(1), Sp, Named("else"), Sp, D(0));
    private static Formula Subtype(Formula variable, Formula type, Formula predicate) =>
        Seq(OpenBrace, variable, Colon, Sp, type, Sp, Mid, Sp, predicate, CloseBrace);
    private static Formula DerangementSlice(Formula family) => Subtype(Pi, Mem(family, N()),
        Call("IsDerangement", Call("val", Pi)));

    private static Formula ContainsFormula()
    {
        var positionMap = F.Id("f");
        var first = F.Id("i");
        var second = F.Id("j");
        return Disp(Seq(BoundPair(K(), N(), Naturals()), Bound(SigmaLower, Perm(K())),
            Bound(Pi, Perm(N())), Call("Contains", SigmaLower, Pi), Sp, Leftrightarrow, Sp,
            Parenthesized(Seq(Exists, Sp, positionMap, Colon, Sp,
                Call("OrderEmbedding", Fin(K()), Fin(N())), Comma, Sp,
                BoundPair(first, second, Fin(K())),
                Parenthesized(Seq(Apply(SigmaLower, first), Sp, Lt, Sp,
                    Apply(SigmaLower, second), Sp, Leftrightarrow, Sp,
                    Apply(Pi, Apply(positionMap, first)), Sp, Lt, Sp,
                    Apply(Pi, Apply(positionMap, second))))))));
    }

    private static Formula Downset(Formula family) => Seq(
        BoundPair(K(), N(), Naturals()), Bound(SigmaLower, Perm(K())), Bound(Pi, Perm(N())),
        Member(Pi, Mem(family, N())), Sp, Implies, Sp,
        Call("Contains", SigmaLower, Pi), Sp, Implies, Sp, Member(SigmaLower, Mem(family, K())));

    private static Formula ClassFormula() => Disp(Seq(Named("PermClass"), Sp, Eq, Sp,
        OpenBrace, C(), Sp, Mid, Sp,
        Parenthesized(Seq(Call("mem", C()), Colon, Sp,
            Parenthesized(Seq(N(), Colon, Sp, Naturals())), Sp, To, Sp, Call("Set", Perm(N())))),
        Sp, Land, Sp, Parenthesized(Seq(Call("downset", C()), Colon, Sp, Downset(C()))), CloseBrace));

    private static Formula DerangementFormula()
    {
        var position = F.Id("i");
        return Disp(Seq(Bound(N(), Naturals()), Bound(Pi, Perm(N())),
            Call("IsDerangement", Pi), Sp, Leftrightarrow, Sp,
            Parenthesized(Seq(Bound(position, Fin(N())),
                Apply(Pi, position), Sp, Neq, Sp, position))));
    }

    private static Formula Av12Formula()
    {
        var first = F.Id("i");
        var second = F.Id("j");
        return Disp(new Formula.Aligned([
            Seq(Bound(N(), Naturals()), Mem(Av(), N()), Sp, Eq, Sp,
                Subtype(Pi, Perm(N()), Parenthesized(Seq(BoundPair(first, second, Fin(N())),
                    first, Sp, Lt, Sp, second, Sp, Implies, Sp,
                    Apply(Pi, second), Sp, Lt, Sp, Apply(Pi, first))))),
            Seq(Call("downset", Av()), Colon, Sp, Downset(Av()))
        ]));
    }

    private static Formula MembershipFormula() => Disp(Seq(Bound(N(), Naturals()),
        Bound(Pi, Perm(N())), Member(Pi, Mem(Av(), N())), Sp, Leftrightarrow, Sp,
        Pi, Sp, Eq, Sp, Rev(N())));

    private static Formula FixedFormula()
    {
        var position = F.Id("i");
        return Disp(Seq(Bound(N(), Naturals()), Bound(position, Fin(N())),
            Apply(Rev(N()), position), Sp, Eq, Sp, position, Sp, Leftrightarrow, Sp,
            D(2), Sp, Times, Sp, Call("val", position), Sp, Plus, Sp, D(1), Sp, Eq, Sp, N()));
    }

    private static Formula ParityFormula() => Disp(Seq(Bound(N(), Naturals()),
        Call("IsDerangement", Rev(N())), Sp, Leftrightarrow, Sp, Call("Even", N())));
    private static Formula CardFormula() => Disp(Seq(Bound(N(), Naturals()),
        Cardinality(Mem(Av(), N())), Sp, Eq, Sp, D(1)));
    private static Formula DerangementCardFormula() => Disp(Seq(Bound(N(), Naturals()),
        Cardinality(DerangementSlice(Av())), Sp, Eq, Sp, ParityValue()));
    private static Formula RatioDefinitionFormula() => Disp(Seq(
        Bound(C(), Named("PermClass")), Bound(N(), Naturals()), Ratio(C(), N()), Sp, Eq, Sp,
        new Formula.Fraction(Call("real", Cardinality(DerangementSlice(C()))),
            Call("real", Cardinality(Mem(C(), N()))))));
    private static Formula RatioFormula() => Disp(Seq(Bound(N(), Naturals()),
        Ratio(Av(), N()), Sp, Eq, Sp, ParityValue()));
    private static Formula NoLimit(Formula family) => Seq(Neg, Sp, Parenthesized(Seq(
        Exists, Sp, F.Id("L"), Colon, Sp, Reals(), Comma, Sp,
        Call("Tendsto", Call("ratio", family), Named("atTop"), Call("nhds", F.Id("L"))))));
}
