using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PureState;

internal sealed class RecordCoherenceComplementarityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized pure records obey exact distinguishability-coherence complementarity.",
        H("Pure Record Distinguishability and Coherence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pure-record-distinguishability-coherence-complementarity"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/PureState/RecordCoherenceComplementarity."
                    + "pure_record_distinguishability_coherence_complementarity"),
                H("Pure-record distinguishability and coherence are complementary"),
                StatementSource.FromAuthor(ComplementarityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let eL and eR be normalized pure record vectors. Their overlap is c, "
                        + "the retained coherence is V = |c|, and the optimal equal-prior "
                        + "distinguishability is D = sqrt(1 - V^2).")),
                    Paragraph(Text(
                        "The theorem retains the exact identity D^2 + V^2 = 1 and both overlap "
                        + "endpoints. Zero overlap gives perfect distinguishability and zero "
                        + "visibility; unit visibility gives zero distinguishability.")),
                    Paragraph(Text(
                        "The operational consequence is explicit: perfect distinguishability "
                        + "forces c to annihilate every unread off-diagonal amplitude. Conversely, "
                        + "complete retained coherence leaves no distinguishability.")),
                    Paragraph(Text(
                        "Loogle, LeanSearch, and the pinned Mathlib tree identify "
                        + "norm_inner_le_norm and Real.sq_sqrt as the exact declarations applied "
                        + "by the Lean proof."))),
                DescribeRole.Theorem))));

    private static Formula ComplementarityFormula()
    {
        Formula left = Seq(F.Id("e"), Underscore, Grp(F.Id("L")));
        Formula right = Seq(F.Id("e"), Underscore, Grp(F.Id("R")));
        Formula c = F.Id("c");
        Formula visibility = F.Id("V");
        Formula distinguishability = F.Id("D");
        Formula absC = Seq(Lvert, Sp, c, Sp, Rvert);

        return Disp(Seq(
            Forall, Sp, F.Id("E"), Colon, Sp,
            Operatorname, Grp(F.Id("InnerProductSpace")), Underscore,
            Grp(Mathbb, Grp(F.Id("C"))), Comma, Esc,
            left, Comma, Sp, right, InMacro, Sp, F.Id("E"), Comma, Esc,
            Vert, Sp, left, Sp, Vert, Sp, Eq, Sp, D(1), Sp, Land, Sp,
            Vert, Sp, right, Sp, Vert, Sp, Eq, Sp, D(1), Comma, RowBreak,
            c, Sp, Eq, Sp, Langle, Sp, left, Comma, Sp, right, Sp, Rangle, Comma, Sp,
            visibility, Sp, Eq, Sp, absC, Comma, Sp,
            distinguishability, Sp, Eq, Sp,
            Sqrt, Grp(D(1), Sp, Minus, Sp, visibility, Caret, Grp(D(2))), Sp,
            Rightarrow, RowBreak,
            distinguishability, Caret, Grp(D(2)), Sp, Plus, Sp,
            visibility, Caret, Grp(D(2)), Sp, Eq, Sp, D(1), Sp, Land, RowBreak,
            Open, c, Sp, Eq, Sp, D(0), Sp, Rightarrow, Sp,
            distinguishability, Sp, Eq, Sp, D(1), Sp, Land, Sp,
            visibility, Sp, Eq, Sp, D(0), Close, Sp, Land, RowBreak,
            Open, visibility, Sp, Eq, Sp, D(1), Sp, Rightarrow, Sp,
            distinguishability, Sp, Eq, Sp, D(0), Sp, Land, Sp,
            visibility, Sp, Eq, Sp, D(1), Close, Sp, Land, RowBreak,
            Open, distinguishability, Sp, Eq, Sp, D(1), Sp, Rightarrow, Sp,
            visibility, Sp, Eq, Sp, D(0), Sp, Land, Sp,
            Forall, Sp, Rho, InMacro, Sp, Mathbb, Grp(F.Id("C")), Comma, Esc,
            c, Rho, Sp, Eq, Sp, D(0), Close, Sp, Land, RowBreak,
            Open, visibility, Sp, Eq, Sp, D(1), Sp, Rightarrow, Sp,
            distinguishability, Sp, Eq, Sp, D(0), Close, Dot));
    }
}
