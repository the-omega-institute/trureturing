using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class NativeWeightedBaseRankSaturationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/NativeWeightedBaseRankSaturation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite native matroid minimum-weight bases are characterized by every real threshold rank.",
        H("Native weighted bases and threshold-rank saturation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("native-weighted-base-weight"),
                DeclarationHandle.Create(Module + ".baseWeight"),
                H("The actual finite weight of a base"),
                StatementSource.FromAuthor(BaseWeightFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite carrier, baseWeight is the finite sum of the given real weight "
                        + "function over the actual base set. The ground is not silently replaced "
                        + "by the carrier."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("native-weighted-lower-weight-set"),
                DeclarationHandle.Create(Module + ".lowerWeightSet"),
                H("The native lower threshold set"),
                StatementSource.FromAuthor(LowerWeightSetFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The threshold set retains precisely elements of the native ground M.E whose "
                        + "real weight is at most t."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("native-weighted-base-rank-saturation"),
                DeclarationHandle.Create(Module + ".native_weighted_base_rank_saturation"),
                H("Attainment and the complete every-base threshold-rank iff"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every universe u, every finite carrier E, every native matroid M on E, "
                            + "and every real weight function w, a minimum-weight base exists. For "
                            + "each base B, minimum total weight among all bases is equivalent to "
                            + "saturating the native rank of every real lower threshold: the finite "
                            + "cardinality of B intersect {e in M.E | w(e) <= t} equals the native "
                            + "eRk of that set cast with toNat.")),
                    Paragraph(Text(
                        "The proof uses direct finite attainment over the set of all bases. The forward "
                            + "direction is the native exchange argument: an unsaturated threshold admits "
                            + "a cheaper base exchange. The reverse direction compares sorted finite base "
                            + "weights from all threshold prefix inequalities, so ties, zero weights and "
                            + "signed weights remain in scope.")),
                    Paragraph(Text(
                        "The statement includes empty carriers and grounds, rank zero, loops, coloops, "
                            + "proper native grounds, nonrepresentable matroids and repeated real weights. "
                            + "It adds no nonempty-ground, positive-rank, positivity, distinctness, supplied "
                            + "optimum, rank-profile or finite-state premise, and it makes no algorithmic, "
                            + "complexity or oracle claim.")),
                    Paragraph(Text(
                        "Oki--Schwarcz, arXiv:2511.16021v3, Theorem 2.1 ("
                            + "https://arxiv.org/abs/2511.16021v3) is recorded only as a rank-increment "
                            + "minimum-value supplier. It is not the literal every-base, every-real-threshold "
                            + "iff stated here; no originality or external open-problem-resolution claim is "
                            + "made."))),
                DescribeRole.Theorem))));

    private static Formula MainFormula()
    {
        Formula u = F.Id("u"), e = F.Id("E"), m = F.Id("M"), w = F.Id("w");
        Formula b = F.Id("B"), c = F.Id("C"), t = F.Id("t");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula setE = Call("Set", e);
        Formula matroidE = Call("Matroid", e);
        Formula isBase(Formula x) => Seq(m, Dot, Operatorname, Grp(F.Id("IsBase")), Sp, x);
        Formula total(Formula x) => Call("baseWeight", w, x);
        Formula lower(Formula x) => Call("lowerWeightSet", m, w, x);
        Formula inter(Formula left, Formula right) => Seq(left, Sp,
            Operatorname, Grp(F.Id("inter")), Sp, right);
        Formula ncard(Formula x) => Call("ncard", x);
        Formula erank(Formula x) => Seq(m, Dot, Operatorname, Grp(F.Id("eRk")), Open, x, Close);
        Formula toNat(Formula x) => Seq(x, Dot, Operatorname, Grp(F.Id("toNat")));
        Formula saturation = Seq(ncard(inter(b, lower(t))), Sp, Eq, Sp,
            toNat(erank(lower(t))));
        Formula minimum(Formula x) => Seq(Forall, Sp, c, Colon, Sp, setE, Comma, Sp,
            isBase(c), Sp, Rightarrow, Sp, total(b), Sp, Leq, Sp, total(c));
        Formula attainment = Seq(Exists, Sp, b, Colon, Sp, setE, Comma, Sp,
            isBase(b), Sp, Land, Sp, minimum(b));
        Formula iff = Seq(Open, minimum(b), Sp, Iff, Sp,
            Seq(Forall, Sp, t, Colon, Sp, real, Comma, Sp, saturation), Close);
        Formula body = Seq(attainment, Sp, Land, Sp,
            Forall, Sp, b, Colon, Sp, setE, Comma, Sp, isBase(b), Sp, Rightarrow, Sp, iff);
        return Disp(Seq(
            Forall, Sp, u, Colon, Sp, type, Comma, Sp,
            Forall, Sp, e, Colon, Sp, type, Sp, u, Comma, Sp,
            OpenBracket, Call("Finite", e), CloseBracket, Comma, Sp,
            Forall, Sp, m, Colon, Sp, matroidE, Comma, Sp,
            Forall, Sp, w, Colon, Sp, new Formula.TypeArrow(e, real), Comma, Sp,
            body, Dot));
    }

    private static Formula BaseWeightFormula()
    {
        Formula w = F.Id("w"), b = F.Id("B"), e = F.Id("e");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula setE = Call("Set", F.Id("E"));
        Formula sumIndex = Seq(e, Sp, InMacro, Sp,
            Call("toFinite", b), Dot, Operatorname, Grp(F.Id("toFinset")));
        Formula sum = new Formula.Subscript(Sum, Grp(sumIndex));
        return Disp(Seq(Forall, Sp, F.Id("E"), Colon, Sp, setE, Comma, Sp,
            Forall, Sp, w, Colon, Sp, new Formula.TypeArrow(F.Id("E"), real), Comma, Sp,
            Forall, Sp, b, Colon, Sp, setE, Comma, Sp,
            Call("baseWeight", w, b), Sp, Eq, Sp,
            sum, Sp, Call("w", e), Dot));
    }

    private static Formula LowerWeightSetFormula()
    {
        Formula e = F.Id("E"), m = F.Id("M"), w = F.Id("w"), t = F.Id("t");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula matroidE = Call("Matroid", e);
        Formula setE = Call("Set", e);
        Formula body = Seq(OpenBrace, F.Id("x"), Sp, Mid, Sp,
            F.Id("x"), Sp, InMacro, Sp, m, Dot, F.Id("E"), Sp, Land, Sp,
            Call("w", F.Id("x")), Sp, Leq, Sp, t, CloseBrace);
        return Disp(Seq(Forall, Sp, e, Colon, Sp, setE, Comma, Sp,
            Forall, Sp, m, Colon, Sp, matroidE, Comma, Sp,
            Forall, Sp, w, Colon, Sp, new Formula.TypeArrow(e, real), Comma, Sp,
            Forall, Sp, t, Colon, Sp, real, Comma, Sp,
            Call("lowerWeightSet", m, w, t), Sp, Eq, Sp, body, Dot));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
}
