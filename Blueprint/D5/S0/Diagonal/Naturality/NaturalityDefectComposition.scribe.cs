using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Diagonal.Naturality;

internal sealed class NaturalityDefectCompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pointwise naturality defects satisfy a Lipschitz composition bound.",
        H("Naturality Defect Under Composition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pointwise-naturality-defect"),
                DeclarationHandle.Create(
                    "D5/S0/Diagonal/Naturality/NaturalityDefectComposition.naturalityDefect"),
                H("Pointwise naturality defect"),
                StatementSource.FromAuthor(NaturalityDefectFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a global map from A to B, projections from A to Am and from B to "
                        + "Bm, and a local map from Am to Bm, the pointwise naturality defect "
                        + "at x is the distance between projecting the global output and "
                        + "applying the local map to the projected input."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("naturality-defect-obeys-the-composition-bound"),
                DeclarationHandle.Create(
                    "D5/S0/Diagonal/Naturality/NaturalityDefectComposition."
                        + "naturality_defect_comp_le"),
                H("Naturality defect obeys the composition bound"),
                StatementSource.FromAuthor(CompositionBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let globalF and globalG be composable global maps, and let localF "
                            + "and localG be their composable local approximations. The local "
                            + "approximation of the composite is localF after localG.")),
                    Paragraph(Text(
                        "If localF is K-Lipschitz, then at every x the defect of globalF after "
                            + "globalG is at most the defect of globalF at globalG(x), plus K "
                            + "times the defect of globalG at x. The proof inserts localF of "
                            + "projectB(globalG(x)), applies the metric triangle inequality, "
                            + "and then applies the imported Lipschitz distance bound.")),
                    Paragraph(Text(
                        "Loogle found dist_triangle and LipschitzWith.dist_le_mul as exact "
                            + "supporting declarations, and the Lean proof imports and applies "
                            + "both. Full-statement pinned-library and repository searches found "
                            + "no duplicate with this typed composition shape."))),
                DescribeRole.Theorem))));

    private static Formula NaturalityDefectFormula()
    {
        Formula a = F.Id("A");
        Formula am = F.Id("Am");
        Formula b = F.Id("B");
        Formula bm = F.Id("Bm");
        Formula projectA = F.Id("projectA");
        Formula projectB = F.Id("projectB");
        Formula globalMap = F.Id("globalMap");
        Formula localMap = F.Id("localMap");
        Formula x = F.Id("x");

        return Disp(Seq(
            Forall, Sp, a, Comma, Sp, am, Comma, Sp, b, Comma, Sp, bm,
            Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("PseudoMetricSpace")), Open, bm, Close,
            CloseBracket, Comma, Esc,
            Forall, Sp,
            projectA, Colon, Sp, new Formula.TypeArrow(a, am), Comma, Sp,
            projectB, Colon, Sp, new Formula.TypeArrow(b, bm), Comma, Esc,
            globalMap, Colon, Sp, new Formula.TypeArrow(a, b), Comma, Sp,
            localMap, Colon, Sp, new Formula.TypeArrow(am, bm), Comma, Sp,
            x, Colon, Sp, a, Comma, Esc,
            Call("naturalityDefect", projectA, projectB, globalMap, localMap, x),
            Sp, Eq, Sp,
            Call("dist", Call("projectB", Call("globalMap", x)),
                Call("localMap", Call("projectA", x))), Dot));
    }

    private static Formula CompositionBoundFormula()
    {
        Formula a = F.Id("A");
        Formula am = F.Id("Am");
        Formula b = F.Id("B");
        Formula bm = F.Id("Bm");
        Formula c = F.Id("C");
        Formula cm = F.Id("Cm");
        Formula projectA = F.Id("projectA");
        Formula projectB = F.Id("projectB");
        Formula projectC = F.Id("projectC");
        Formula globalF = F.Id("globalF");
        Formula localF = F.Id("localF");
        Formula globalG = F.Id("globalG");
        Formula localG = F.Id("localG");
        Formula k = F.Id("K");
        Formula x = F.Id("x");

        return Disp(Seq(
            Forall, Sp, a, Comma, Sp, am, Comma, Sp, b, Comma, Sp, bm, Comma, Sp,
            c, Comma, Sp, cm, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("PseudoMetricSpace")), Open, bm, Close,
            CloseBracket, Comma, Sp,
            OpenBracket, Operatorname, Grp(F.Id("PseudoMetricSpace")), Open, cm, Close,
            CloseBracket, Comma, Esc,
            Forall, Sp,
            projectA, Colon, Sp, new Formula.TypeArrow(a, am), Comma, Sp,
            projectB, Colon, Sp, new Formula.TypeArrow(b, bm), Comma, Sp,
            projectC, Colon, Sp, new Formula.TypeArrow(c, cm), Comma, Esc,
            globalF, Colon, Sp, new Formula.TypeArrow(b, c), Comma, Sp,
            localF, Colon, Sp, new Formula.TypeArrow(bm, cm), Comma, Sp,
            globalG, Colon, Sp, new Formula.TypeArrow(a, b), Comma, Sp,
            localG, Colon, Sp, new Formula.TypeArrow(am, bm), Comma, Esc,
            k, Colon, Sp, Operatorname, Grp(F.Id("NNReal")), Comma, Sp,
            x, Colon, Sp, a, Comma, Esc,
            Call("LipschitzWith", k, localF), Sp, Rightarrow, Sp,
            Call("naturalityDefect", projectA, projectC,
                Seq(globalF, Sp, Circ, Sp, globalG),
                Seq(localF, Sp, Circ, Sp, localG), x),
            Sp, Leq, Sp,
            Call("naturalityDefect", projectB, projectC, globalF, localF,
                Call("globalG", x)),
            Sp, Plus, Sp, k, Sp, Cdot, Sp,
            Call("naturalityDefect", projectA, projectB, globalG, localG, x), Dot));
    }
}
