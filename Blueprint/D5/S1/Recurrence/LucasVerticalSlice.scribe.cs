using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class LucasVerticalSliceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/LucasVerticalSlice.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/fiebigmbirikaspilker2025lucas");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Vertical slices admit criteria in terms of two consecutive traces, integer companion powers under a unit discriminant, and half the companion period when four is nonzero. The unit-discriminant hypothesis is not removable.",
        H("Lucas Vertical Slices"),
        Blocks(
            Paragraph(Text(
                "Let R be any commutative ring, p an element of R, and q a unit of R. "
                    + "A vertical slice is an integer shift s for which lucasV(p, q, n) + "
                    + "lucasV(p, q, n + s) = 0 for every integer n. The first criterion "
                    + "characterizes its existence by two consecutive companion traces: "
                    + "lucasV(p, q, s) = -2 and lucasV(p, q, s + 1) = -p. The second "
                    + "criterion, under the hypothesis that p squared minus 4q is a unit, "
                    + "characterizes its existence by an integer power of the companion "
                    + "matrix equal to minus one. The first criterion carries no hypothesis "
                    + "and is the one that answers a question Fiebig, Mbirika and Spilker "
                    + "leave open, for every unit q and with no restriction on the order "
                    + "statistic or the discriminant; the second refines it under a "
                    + "hypothesis that result proves is not removable. The proofs are "
                    + "repository work, with the source paper acknowledged.")),
            Paragraph(Text(
                "The third criterion, verticalSlice_iff_half_companionPeriod, assumes "
                    + "that four is nonzero in R. It states that a vertical slice exists "
                    + "exactly when there is a natural number T such that the companion "
                    + "period equals 2T and the traces at T and T + 1 are -2 and -p. "
                    + "The non-removability of the nonzero-four hypothesis in the "
                    + "half-period criterion is measured but not proved.")),
            Node("verticalSlice_iff_two_traces", "Two consecutive traces characterize a slice",
                TwoTracesFormula(),
                "Over every commutative ring R, the existence of a shift cancelling "
                    + "every companion trace is equivalent to the existence of a shift "
                    + "with the two stated trace values. Both shifts range over all "
                    + "integers, and q ranges over all units of R. This criterion carries "
                    + "no hypothesis, so it answers the question Fiebig, Mbirika and Spilker "
                    + "leave open without restricting q, the order statistic, or the "
                    + "discriminant.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("fiebig-mbirika-spilker-vertical-slice"),
                    ResolutionKind.Proved)),
            Node("verticalSlice_iff_neg_one_mem_zpowers", "A unit discriminant detects minus one",
                UnitDiscriminantFormula(),
                "If p squared minus 4q is a unit, a vertical slice exists exactly when "
                    + "an integer power of companion(p, q) is minus the identity. "
                    + "The scalar q in the discriminant is the underlying element of R "
                    + "of the unit q. No hypothesis restricts the order statistic.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("result", "The unit-discriminant hypothesis is not removable",
                ResultFormula(),
                "The definition claim asserts the companion-power equivalence over "
                    + "every ZMod(m) without a discriminant hypothesis. The theorem "
                    + "result proves that the unit-discriminant hypothesis is not "
                    + "removable by refuting claim, with the witness p = 4, q = 1, "
                    + "modulus 6. The shift s = 1 gives a vertical slice, but no integer "
                    + "companion power equals minus one. The displayed negation scopes "
                    + "over the entire universal claim.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("lucas-vertical-slice-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula Typed(string name, Formula type) => Seq(F.Id(name), Colon, Sp, type);
    private static Formula Bind(string name, Formula type) => Seq(Forall, Sp, Typed(name, type), Comma);
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Paren(Formula a) => Seq(Left, Open, a, Right, Close);
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Units(Formula a) => Call("Units", a);
    private static Formula P() => F.Id("p");
    private static Formula Q() => F.Id("q");
    private static Formula V(Formula n) => Call("lucasV", P(), Q(), n);
    private static Formula Slice() => Paren(Seq(
        Exists, Sp, Typed("s", Integers()), Comma, Sp,
        Bind("n", Integers()), Sp,
        Equal(Seq(V(F.Id("n")), Sp, Plus, Sp,
            V(Seq(F.Id("n"), Sp, Plus, Sp, F.Id("s")))), D(0))));
    private static Formula MinusOnePower() => Paren(Seq(
        Exists, Sp, Typed("s", Integers()), Comma, Sp,
        Equal(new Formula.Power(Call("companion", P(), Q()), F.Id("s")), Seq(Minus, D(1)))));
    private static Formula PowerCriterion() => Seq(Slice(), Sp, Iff, Sp, MinusOnePower());
    private static Formula TwoTracesFormula() => Disp(Seq(
        Bind("p", F.Id("R")), Sp, Bind("q", Units(F.Id("R"))), Sp,
        Slice(), Sp, Iff, Sp,
        Paren(Seq(Exists, Sp, Typed("s", Integers()), Comma, Sp,
            Paren(Seq(Equal(V(F.Id("s")), Seq(Minus, D(2))), Sp, Land, Sp,
                Equal(V(Seq(F.Id("s"), Sp, Plus, Sp, D(1))), Seq(Minus, P()))))))));
    private static Formula UnitDiscriminantFormula() => Disp(Seq(
        Bind("p", F.Id("R")), Sp, Bind("q", Units(F.Id("R"))), Sp,
        Call("IsUnit", Seq(new Formula.Power(P(), D(2)), Sp, Minus, Sp,
            D(4), Sp, Cdot, Sp, Call("Cast", Q(), F.Id("R")))), Sp, Rightarrow, Sp,
        Paren(PowerCriterion())));
    private static Formula ResultFormula() => Disp(Seq(Neg, Sp, Paren(Seq(
        Bind("m", Naturals()), Sp,
        Bind("p", Call("ZMod", F.Id("m"))), Sp,
        Bind("q", Units(Call("ZMod", F.Id("m")))), Sp,
        Paren(PowerCriterion())))));
}
