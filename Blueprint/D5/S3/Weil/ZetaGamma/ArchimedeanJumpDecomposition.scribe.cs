using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma;

internal sealed class ArchimedeanJumpDecompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The completed-zeta Archimedean term is its mass contribution plus a nonnegative "
            + "continuous translation energy.",
        H("Archimedean Jump Decomposition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("archimedean-jump-decomposition"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/ZetaGamma/ArchimedeanJumpDecomposition."
                        + "archimedean_jump_decomposition"),
                H("Archimedean jump decomposition"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The test function lies in the canonical carrier of even smooth compactly "
                            + "supported complex-valued functions. The displayed hArch premise is "
                            + "the exact integrability witness consumed by archimedeanTerm.")),
                    Paragraph(Text(
                        "The jump density is exp(-x/2)/(1-exp(-2x)) on positive scales, and the "
                            + "jump energy integrates the squared displacement of f by translation "
                            + "against that density. The proof derives its Levy representation from "
                            + "the frozen digamma series and applies Fourier inversion and Tonelli.")),
                    Paragraph(Text(
                        "The first public conjunct is the exact complex identity. The second "
                            + "public conjunct records positivity of the independently constructed "
                            + "continuous jump energy."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula TheoremFormula()
    {
        Formula test = F.Id("f");
        Formula hArch = F.Id("hArch");
        Formula convolutionSquare = Call("convolutionSquare", test);
        Formula energy = Call("archimedeanJumpEnergy", test);
        Formula constant = Seq(
            Operatorname,
            Grp(F.Id("archimedeanConstant")));
        Formula decomposition = new Formula.Relation(
            Call("archimedeanTerm", convolutionSquare, hArch),
            FormulaRelationOperator.Equal,
            new Formula.Binary(
                new Formula.Binary(
                    constant,
                    FormulaBinaryOperator.Multiply,
                    Call("l2Mass", test)),
                FormulaBinaryOperator.Add,
                energy));
        Formula nonnegative = new Formula.Relation(
            D(0),
            FormulaRelationOperator.LessThanOrEqual,
            energy);
        Formula conclusion = new Formula.Logic(
            decomposition,
            FormulaLogicOperator.And,
            nonnegative);

        return Disp(Seq(
            Forall, Sp, test, InMacro, Sp, Mathcal, Grp(F.Id("W")), Comma, Sp,
            hArch, Colon, Sp,
            Operatorname, Grp(F.Id("ArchimedeanConvergent")), Open,
            convolutionSquare, Close, Sp, Rightarrow, Sp, conclusion));
    }
}
