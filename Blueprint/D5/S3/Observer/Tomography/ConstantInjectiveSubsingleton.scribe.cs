using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Tomography;

internal sealed class ConstantInjectiveSubsingletonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An injective constant readout forces its state carrier to be a subsingleton.",
        H("Constant Injective Subsingleton"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("constant-injective-readout-has-at-most-one-state"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Tomography/ConstantInjectiveSubsingleton."
                        + "constant_injective_subsingleton"),
                H("A constant injective readout has at most one state"),
                StatementSource.FromAuthor(SubsingletonFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let q be a readout from an arbitrary state type X to an arbitrary "
                            + "codomain Y. Assume independently that q is injective and that all "
                            + "of its values are equal.")),
                    Paragraph(Text(
                        "Constantness equates the readouts of any two states, and injectivity "
                            + "then equates the states themselves. Thus X is a subsingleton, "
                            + "which directly states that X has at most one element.")),
                    Paragraph(Text(
                        "Pinned Mathlib's Injective.subsingleton theorem assumes the entire "
                            + "codomain is a subsingleton and therefore is not an exact source "
                            + "match. Repository and pinned-library searches found no exact "
                            + "theorem with the two displayed premises.")),
                    Paragraph(Text(
                        "The subsequent source discussion about replacing one scalar readout "
                            + "by a binary structure is qualitative and supplies no in-scope "
                            + "binary-structure predicate, so it is not promoted to a conjunct."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula SubsingletonFormula()
    {
        Formula stateType = F.Id("X");
        Formula outputType = F.Id("Y");
        Formula readout = F.Id("q");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula constant = Seq(
            Forall, Sp, left, Comma, Sp, right, InMacro, Sp, stateType, Comma, Sp,
            Call("q", left), Sp, Eq, Sp, Call("q", right));

        return Disp(Seq(
            Forall, Sp, stateType, Comma, Sp, outputType,
            Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Esc,
            Forall, Sp, readout, Colon, Sp,
            new Formula.TypeArrow(stateType, outputType), Comma, Esc,
            Call("Injective", readout), Sp, Land, Sp, Grp(constant),
            Sp, Rightarrow, Sp, Call("Subsingleton", stateType), Dot));
    }
}
