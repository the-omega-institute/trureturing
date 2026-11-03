using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Restoration;

internal sealed class PositiveRelationSupportNecessityDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/ConceptDynamics/Restoration/PositiveRelationSupportNecessity.";
    private static Formula A => F.Id("A");
    private static Formula B => F.Id("B");
    private static Formula L => F.Id("L");
    private static Formula R => F.Id("R");
    private static Formula E => F.Id("E");
    private static Formula Dd => F.Id("D");
    private static Formula Lm => F.Id("l");
    private static Formula Rm => F.Id("r");
    private static Formula Pair(Formula a, Formula b) => Seq(Open, a, Comma, Sp, b, Close);
    private static Formula Product(Formula a, Formula b) => Seq(a, Sp, Times, Sp, b);
    private static Formula Emb(Formula a, Formula b) => Call("Embedding", a, b);
    private static Formula Rel(Formula a, Formula b) => Call("SetRel", a, b);
    private static Formula App(Formula f, Formula x) => Seq(f, Open, x, Close);
    private static Formula Tr(Formula l, Formula r) => Call("transport", E, l, r);
    private static Formula Mem(Formula x, Formula s) => Seq(x, Sp, InMacro, Sp, s);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Sp, Subseteq, Sp, b);
    private static Formula Ne(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula All(string x, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(x), Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(string x, Formula type, Formula body) =>
        Seq(Exists, Sp, F.Id(x), Colon, Sp, type, Comma, Sp, body);
    private static Formula Imp(Formula premise, Formula result) =>
        Seq(Open, premise, Close, Sp, Rightarrow, RowBreak, Grp(), result);
    private static Formula Conj(params Formula[] items) =>
        Seq(items.SelectMany((x, i) => i == 0
            ? new[] { Open, x, Close }
            : new[] { Sp, Land, RowBreak, Grp(), Open, x, Close }).ToArray());
    private static Formula Types(Formula body) =>
        All("A", F.Id("Type"), All("B", F.Id("Type"),
            All("L", F.Id("Type"), All("R", F.Id("Type"), body))));
    private static Formula Data(Formula evidenceType, Formula body) =>
        All("E", Rel(A, B), All("l", Emb(A, L),
            All("r", Emb(B, R), All("D", evidenceType, body))));
    private static Formula Incident(bool left, Formula vertex) => left
        ? Some("b", B, Mem(Pair(vertex, F.Id("b")), E))
        : Some("a", A, Mem(Pair(F.Id("a"), vertex), E));
    private static Formula Instances(Formula body) => Seq(
        OpenBracket, Call("Fintype", A), CloseBracket, Comma, Sp,
        OpenBracket, Call("Fintype", B), CloseBracket, Comma, Sp,
        OpenBracket, Call("Fintype", L), CloseBracket, Comma, Sp,
        OpenBracket, Call("Fintype", R), CloseBracket, Comma, Sp,
        OpenBracket, Call("DecidableEq", L), CloseBracket, Comma, Sp,
        OpenBracket, Call("DecidableEq", R), CloseBracket, Comma, RowBreak, Grp(), body);
    private static Formula Card(Formula x) => Call("card", x);
    private static Formula Bound => Call("max", Card(A), Card(B));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unrestricted full injections and unused ambient labels force positive "
            + "certificates to expose every nonisolated endpoint on both sides.",
        H("Positive Relation Support Necessity"),
        Blocks(
            Describe.Lean(DescribeId.Create("transported-full-relation"),
                DeclarationHandle.Create(Owner + "transport"), H("Transport by full injections"),
                StatementSource.FromAuthor(TransportFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Embedding denotes a full injective function, SetRel a set "
                    + "of ordered pairs, and image and ProdMap have their usual set and product "
                    + "meanings. The transported target contains the entire source relation."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("left-label-transposition-competitor"),
                DeclarationHandle.Create(Owner + "unexposed_left_label_competitor"),
                H("An unexposed left label admits a competing full injection"),
                StatementSource.FromAuthor(CompetitorFormula(true)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Compose the full left embedding with the ambient "
                    + "transposition exchanging its selected label and the unused label. "
                    + "Injectivity follows from composition with an equivalence. Every evidence "
                    + "edge avoids the selected endpoint, so its two labels stay fixed. An "
                    + "incident edge now uses the fresh label, which no old edge uses. "
                    + "No finiteness assumption is needed for this construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("right-label-transposition-competitor"),
                DeclarationHandle.Create(Owner + "unexposed_right_label_competitor"),
                H("An unexposed right label admits a competing full injection"),
                StatementSource.FromAuthor(CompetitorFormula(false)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The right embedding is composed with its ambient "
                    + "transposition. The same source relation and the original left embedding "
                    + "remain in the competitor. Its fresh right label witnesses a genuinely "
                    + "different transported target while all acquired positive pairs survive."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("positive-support-and-slot-lower-bound"),
                DeclarationHandle.Create(Owner + "positive_certificate_support_lower_bound"),
                H("Target-constant positive evidence exposes both supports"),
                StatementSource.FromAuthor(SupportFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The version domain contains every pair of full embeddings "
                        + "of this same source. Attainment supplies the original pair, and "
                        + "constancy is required over every compatible pair. Ambient cardinal "
                        + "slack produces an unused label on each side. If a used label were "
                        + "missing, the corresponding competitor would contradict constancy.")),
                    Paragraph(Text("The domain and codomain of the evidence are its two "
                        + "endpoint projections. Each projection has at most as many elements "
                        + "as the distinct-pair set. A completed-slot list has at least as many "
                        + "positions as its deduplicated set, so repetitions retain their cost. "
                        + "Support exposure is a necessary condition and is not asserted sufficient."))),
                DescribeRole.Theorem),
            Paragraph(Text("For the literal two-source relations of PCR.1 and UJB.9001 take "
                + "the field F with three elements, "
                + "A = (F² excluding zero) × F² and T = F³ × F². The right endpoint "
                + "retains every third w coordinate and every z coordinate for both sources. "
                + "Thus the literal endpoint cardinalities are (9 − 1) × 9 = 72 and "
                + "27 × 9 = 243. The label types are seven-bit and eight-bit words, of "
                + "cardinalities 2⁷ = 128 and 2⁸ = 256. Both ambient inequalities are strict.")),
            Paragraph(Text("The source-zero equations are B₀(v,w) = "
                + "(v₁w₁ + v₂w₂, v₁w₂ + v₂w₃), and the source-one equations are "
                + "B₁(v,w) = (v₁w₁ − v₂w₂, v₂w₁ + v₁w₂). Incidence means "
                + "Bᵢ(v,w) = s and ignores z. UJB Proposition 3.2 and Theorem 15.2 "
                + "give literal left degree 27 and right degree 8 for each source; these "
                + "positive degrees supply the two nonisolation hypotheses. They refer "
                + "to literal endpoints, without replacing either relation by its quotient.")),
            Paragraph(Text("Fix whichever source is actual and supported. Source zero is "
                + "supported when θ < 1 and source one when θ > 0, with 0 ≤ θ ≤ 1. "
                + "The prior weight of each full map pair is respectively (1 − θ) or θ "
                + "divided by (128)₇₂(256)₂₄₃. A transposition changes neither source nor "
                + "weight positivity. Consequently every same-source competitor constructed "
                + "here belongs to the original supported family, including at θ = 0 or "
                + "θ = 1 for the supported branch. No premise comparing the two sources is needed.")),
            Paragraph(Text("A certificate constant over the full supported family is constant "
                + "over all full embeddings of its actual source. Apply the general theorem "
                + "to that restricted universal premise, keeping the actual maps and attained "
                + "distinct positive set D. Its conclusions expose the full images on both "
                + "sides and yield max(72,243) = 243 ≤ |D| ≤ the number of completed slots. "
                + "The assertion uses positive complete pairs alone: no absent pair is a negative "
                + "query and no partially acquired bits or pre-supplied support dictionary enter D.")),
            Paragraph(Text("The generic construction and lower bound are kernel checked. "
                + "The application requires a canonical Lean identification of the literal "
                + "UJB relations, their endpoint counts and their degree suppliers; those "
                + "source-specific suppliers are not provided by this module. Thus this "
                + "exposition records their parameter correspondence and conditional derivation, "
                + "and does not assert a compiled theorem for the entire original preparation, "
                + "positive prior, native acquisition contract or numerical certificate bounds "
                + "576 and 324. The abstract target-constancy interpretation agrees with "
                + "TargetRecoveryCriterion.target_recovery_criterion; the new mathematical "
                + "input here is the competing full injection, rather than that recovery criterion."))
        )));

    private static Formula TransportFormula() => Disp(Types(
        All("E", Rel(A, B), All("l", Emb(A, L), All("r", Emb(B, R),
            Equal(Tr(Lm, Rm), Call("image", Call("ProdMap", Lm, Rm), E)))))));

    private static Formula CompetitorFormula(bool left)
    {
        Formula vertex = F.Id(left ? "a" : "b");
        Formula source = left ? A : B;
        Formula ambient = left ? L : R;
        Formula original = left ? Lm : Rm;
        Formula projection = Call(left ? "dom" : "cod", Dd);
        Formula fresh = F.Id("c");
        Formula alt = F.Id("f");
        Formula x = F.Id("x");
        Formula changed = left ? Tr(alt, Rm) : Tr(Lm, alt);
        Formula conclusion = Some("f", Emb(source, ambient), Conj(
            Equal(App(alt, vertex), fresh),
            All("x", source, Imp(Ne(x, vertex), Equal(App(alt, x), App(original, x)))),
            Sub(Dd, changed), Ne(changed, Tr(Lm, Rm))));
        return Disp(Types(Data(Rel(L, R), All(left ? "a" : "b", source,
            All("c", ambient, Imp(Conj(Sub(Dd, Tr(Lm, Rm)), Incident(left, vertex),
                Seq(Neg, Sp, Mem(App(original, vertex), projection)),
                Seq(Neg, Sp, Mem(fresh, Call("range", original)))), conclusion))))));
    }

    private static Formula SupportFormula()
    {
        Formula f = F.Id("f");
        Formula g = F.Id("g");
        Formula samples = F.Id("s");
        Formula constant = All("f", Emb(A, L), All("g", Emb(B, R),
            Imp(Sub(Dd, Tr(f, g)), Equal(Tr(f, g), Tr(Lm, Rm)))));
        return Disp(Types(Instances(Data(Call("Finset", Product(L, R)), Imp(Conj(
            Sub(Dd, Tr(Lm, Rm)), All("a", A, Incident(true, F.Id("a"))),
            All("b", B, Incident(false, F.Id("b"))),
            Seq(Card(A), Sp, Lt, Sp, Card(L)), Seq(Card(B), Sp, Lt, Sp, Card(R)), constant),
            Conj(Equal(Call("dom", Dd), Call("range", Lm)),
                Equal(Call("cod", Dd), Call("range", Rm)),
                Seq(Bound, Sp, Leq, Sp, Card(Dd)),
                All("s", Call("List", Product(L, R)),
                    Imp(Equal(Call("toFinset", samples), Dd),
                        Seq(Bound, Sp, Leq, Sp, Call("length", samples))))))))));
    }
}
