using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Diagonal.Naturality;

internal sealed class ApproximateDescentCompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform pseudometric errors of approximate descents obey the Lipschitz composition budget.",
        H("Approximate Descent Composition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("uniform-naturality-defect"),
                DeclarationHandle.Create(
                    "D5/S0/Diagonal/Naturality/ApproximateDescentComposition."
                        + "uniformNaturalityDefect"),
                H("Uniform naturality defect"),
                StatementSource.FromAuthor(UniformDefectFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The global defect is constructed from the source interface as the supremum, "
                        + "over source states, of the imported pointwise pseudometric defect."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("approximate-descent-composition-bound"),
                DeclarationHandle.Create(
                    "D5/S0/Diagonal/Naturality/ApproximateDescentComposition."
                        + "approximate_descent_comp_bound"),
                H("Approximate descent composition bound"),
                StatementSource.FromAuthor(CompositionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The maps F and G have local approximations with public pointwise bounds "
                            + "epsilonF and epsilonG. The outer local approximation is L-Lipschitz.")),
                    Paragraph(Text(
                        "The global defect of the composite is at most epsilonG plus L times "
                            + "epsilonF. The proof directly applies the frozen pointwise composition "
                            + "theorem and then takes the supremum.")),
                    Paragraph(Text(
                        "Repository search found the exact pointwise theorem but no existing "
                            + "uniform supremum statement. The imported theorem already applies the "
                            + "pinned metric triangle and Lipschitz distance declarations."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula UniformDefectFormula()
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
            Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, RowBreak, Grp(),
            OpenBracket, Operatorname, Grp(F.Id("PseudoMetricSpace")), Open, bm, Close,
            CloseBracket, Comma, Sp, Forall, Sp,
            projectA, Colon, Sp, Arrow(a, am), Comma, Sp,
            projectB, Colon, Sp, Arrow(b, bm), Comma, RowBreak, Grp(),
            globalMap, Colon, Sp, Arrow(a, b), Comma, Sp,
            localMap, Colon, Sp, Arrow(am, bm), Comma, RowBreak, Grp(),
            Call("uniformNaturalityDefect", projectA, projectB, globalMap, localMap),
            Sp, Eq, Sp, Call("supremum", x,
                Call("naturalityDefect", projectA, projectB, globalMap, localMap, x)), Dot));
    }

    private static Formula CompositionFormula()
    {
        Formula xType = F.Id("X");
        Formula xbar = F.Id("Xbar");
        Formula yType = F.Id("Y");
        Formula ybar = F.Id("Ybar");
        Formula zType = F.Id("Z");
        Formula zbar = F.Id("Zbar");
        Formula projectX = F.Id("projectX");
        Formula projectY = F.Id("projectY");
        Formula projectZ = F.Id("projectZ");
        Formula globalF = F.Id("globalF");
        Formula localF = F.Id("localF");
        Formula globalG = F.Id("globalG");
        Formula localG = F.Id("localG");
        Formula epsilonF = F.Id("epsilonF");
        Formula epsilonG = F.Id("epsilonG");
        Formula ell = F.Id("L");
        Formula x = F.Id("x");
        Formula y = F.Id("y");

        Formula innerBound = Seq(
            Forall, Sp, x, Comma, Sp,
            Call("naturalityDefect", projectX, projectY, globalF, localF, x),
            Sp, Leq, Sp, epsilonF);
        Formula outerBound = Seq(
            Forall, Sp, y, Comma, Sp,
            Call("naturalityDefect", projectY, projectZ, globalG, localG, y),
            Sp, Leq, Sp, epsilonG);
        Formula result = Seq(
            Call("uniformNaturalityDefect", projectX, projectZ,
                Seq(globalG, Sp, Circ, Sp, globalF),
                Seq(localG, Sp, Circ, Sp, localF)),
            Sp, Leq, Sp, epsilonG, Sp, Plus, Sp, ell, Sp, Cdot, Sp, epsilonF);

        return Disp(Seq(
            Forall, Sp, xType, Comma, Sp, xbar, Comma, Sp, yType, Comma, Sp, ybar,
            Comma, Sp, zType, Comma, Sp, zbar, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, RowBreak, Grp(),
            OpenBracket, Operatorname, Grp(F.Id("PseudoMetricSpace")), Open, ybar, Close,
            CloseBracket, Comma, Sp,
            OpenBracket, Operatorname, Grp(F.Id("PseudoMetricSpace")), Open, zbar, Close,
            CloseBracket, Comma, RowBreak, Grp(),
            projectX, Colon, Sp, Arrow(xType, xbar), Comma, Sp,
            projectY, Colon, Sp, Arrow(yType, ybar), Comma, Sp,
            projectZ, Colon, Sp, Arrow(zType, zbar), Comma, RowBreak, Grp(),
            globalF, Colon, Sp, Arrow(xType, yType), Comma, Sp,
            localF, Colon, Sp, Arrow(xbar, ybar), Comma, Sp,
            globalG, Colon, Sp, Arrow(yType, zType), Comma, Sp,
            localG, Colon, Sp, Arrow(ybar, zbar), Comma, RowBreak, Grp(),
            epsilonF, Comma, Sp, epsilonG, Colon, Sp, F.Id("Real"), Comma, Sp,
            ell, Colon, Sp, F.Id("NNReal"), Comma, RowBreak, Grp(),
            Call("Nonempty", xType), Sp, Land, Sp,
            Grp(innerBound), Sp, Land, Sp, Grp(outerBound), Sp, Land, Sp,
            Call("LipschitzWith", ell, localG), Sp, Rightarrow, Sp, result, Dot));
    }
}
