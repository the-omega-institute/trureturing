using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class TwoCopyReadoutFiberDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The real two-copy Bell readout identifies exactly the hidden-phase involution q ↔ 1-q.",
        H("Two-Copy Readout Fiber"), Blocks(
            Paragraph(Text("Use the explicit five-coordinate phase mixture and its real two-copy Bell readout. The fiber theorem classifies every pair of parameters in the closed unit interval that produce the same readout.")),
            Describe.Lean(DescribeId.Create("two-copy-readout-fiber"),
                DeclarationHandle.Create("D5/S3/Quantum/Fibers/TwoCopyReadoutFiber.two_copy_bell_readout_fiber"),
                H("Two-copy Bell readout fiber"),
                StatementSource.FromAuthor(Disp(FiberStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The readout sees the square of the signed coordinate 1 - 2q. Its observational fiber is exactly q = r or q + r = 1, so the residual ambiguity is the involution q ↦ 1-q.")),
                    Paragraph(Text("This is a finite-dimensional statement for the explicit phase-mixture family. It supplies no FIB Source-to-density bridge, physical preparation, or QFT realization."))),
                DescribeRole.Theorem))));

    private static Formula C(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) items.Add(Comma);
            items.Add(arguments[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula FiberStatement()
    {
        var interval = C("IccReal", D(0), D(1));
        var q = F.Id("q");
        var r = F.Id("r");
        var readoutEqual = Equal(C("twoCopyProbability", q), C("twoCopyProbability", r));
        var same = Equal(Typed(q, R()), Typed(r, R()));
        var involuted = Equal(Seq(Typed(q, R()), Plus, Typed(r, R())), D(1));
        var fiber = new Formula.Logic(Parenthesized(same), FormulaLogicOperator.Or,
            Parenthesized(involuted));
        return All("q", interval, All("r", interval,
            new Formula.Logic(Parenthesized(readoutEqual), FormulaLogicOperator.Iff,
                Parenthesized(fiber))));
    }

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula R() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
}
