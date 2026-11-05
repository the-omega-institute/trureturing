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
                + "F = ZMod 3, A = ({v : Fin 2 → F // v ≠ 0}) × (Fin 2 → F), "
                + "and T = (Fin 3 → F) × (Fin 2 → F). The source relations are "
                + "Eᵢ = {((v,s),(w,z)) | Bᵢ(v,w) = s}, with "
                + "B₀(v,w) = (v₁w₁ + v₂w₂, v₁w₂ + v₂w₃) and "
                + "B₁(v,w) = (v₁w₁ − v₂w₂, v₂w₁ + v₁w₂). The full w₃ coordinate "
                + "and all nine z values are retained for both sources.")),
            Paragraph(Text("The nonzero v subtype has cardinality 8, so A has cardinality 8 × 9 = 72, "
                + "and T has cardinality 27 × 9 = 243. The "
                + "the ambient word carriers (Fin 7 → Bool) and (Fin 8 → Bool) have "
                + "cardinalities 128 and 256. Both source relations have every left "
                + "and right endpoint incident; their literal edge sets each have 1944 "
                + "pairs. The strict inequalities 72 < 128 and 243 < 256 provide the "
                + "unused ambient labels required by the support theorem.")),
            Paragraph(Text("For each nonzero v, each Bᵢ(v,−) takes every s value: "
                + "there are exactly three w solutions. Each admits all nine z values, "
                + "giving left degree 27. For fixed (w,z), every one of the eight "
                + "nonzero v values determines exactly one s, giving right degree 8. "
                + "In particular left incidence can take any solution w and z = 0; "
                + "right incidence can take v = (1,0) and s = Bᵢ(v,w). Summing "
                + "the left degrees gives 72 × 27 = 1944, with no coordinate quotient.")),
            Paragraph(Text("For 0 ≤ θ ≤ 1, a full-map generator at source zero has "
                + "weight (1 − θ)/((128)₇₂(256)₂₄₃), and a source-one generator has "
                + "weight θ/((128)₇₂(256)₂₄₃). Thus the zero branch is positive exactly "
                + "when θ < 1 and the one branch exactly when θ > 0. At θ = 0 only "
                + "the zero branch is supported; at θ = 1 only the one branch is "
                + "supported. Any same-source replacement of either full injection keeps "
                + "the source index and has the same positive prior. The denominator is "
                + "strictly positive and equals the number of full injection pairs, "
                + "by Fintype.card_embedding_eq on both carriers.")),
            Paragraph(Text("The exact source application treats a completed history as "
                + "samples : List ((Fin 7 → Bool) × (Fin 8 → Bool)) and D = samples.toFinset. "
                + "Each completed pair is positive attained evidence, and target constancy "
                + "over the supported generator family restricts to the general theorem's "
                + "universal premise over every full injection pair for the actual source. "
                + "Attainment already places the actual supported generator in the compatible "
                + "family, so the constancy premise is not over an empty family. Apply "
                + "positive_certificate_support_lower_bound with its A replaced by this "
                + "literal A, its B by T, its L and R by the two word carriers, its E "
                + "by the actual Eᵢ, and its embeddings by the full λ and ϱ. The source "
                + "incidence and cardinalities discharge every remaining premise. The "
                + "two evidence projections equal range λ and range ϱ; max(72,243) = 243 gives "
                + "243 ≤ D.card and 243 ≤ samples.length for each supported branch.")),
            Paragraph(Text("This application uses only complete positive pairs. Repetitions "
                + "remain completed slots, while absent pairs, partial-bit caches, support "
                + "dictionaries, cross-source identification, and the separate 576- and "
                + "324-pair witness constructions are outside this consequence. The "
                + "source-specific application check is transient evidence for the existing "
                + "general theorem, with no retained specialization declaration. This establishes "
                + "the PCR 4.1 support-necessity consequence only; it supplies no "
                + "preparation procedure, native acquisition contract, or source-bit recovery. "
                + "The retained mathematical content is the general "
                + "support and slot lower bound and this scope-limited correspondence."))
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
