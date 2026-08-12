using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Naming;

internal sealed class DenseGreenClassDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var assumptions = new Formula.Logic(
            Call("Dense", F.Id("P")),
            FormulaLogicOperator.And,
            new Formula.Logic(
                Call("IsOpen", F.Id("G")),
                FormulaLogicOperator.And,
                Call("Nonempty", F.Id("G"))));
        var conclusion = Call("Nonempty", Call("inter", F.Id("G"), F.Id("P")));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Every nonempty open class meets a dense property.",
            H("Dense Properties Meet Every Green Class"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("dense-properties-meet-every-nonempty-open-class"),
                    DeclarationHandle.Create(
                        "D5/S0/Naming/DenseGreenClass.dense_inter_green_class_nonempty"),
                    H("A dense property meets every nonempty open class"),
                    StatementSource.FromAuthor(new Formula.Logic(
                        assumptions,
                        FormulaLogicOperator.Implies,
                        conclusion)),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Let P and G be subsets of an arbitrary topological space. If P is "
                            + "dense and G is nonempty and open, then G intersects P. Thus an open "
                            + "green class cannot refute the dense property by having empty intersection.")),
                        Paragraph(Text(
                            "Pinned Mathlib supplies the exact result as Dense.inter_open_nonempty. "
                            + "The Lean declaration is a thin wrapper that preserves the source's "
                            + "intersection orientation.")),
                        Paragraph(Text(
                            "This is a partial closure of clause (a) only. The safety and liveness "
                            + "decomposition claims, the general property decomposition, and clause (b) "
                            + "on finite observability outside a closed set remain unresolved."))),
                    DescribeRole.Proposition)),
            []));
    }
}
