using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.RefinementFactorization;

internal sealed class InjectiveInterfaceTargetFactorizationDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula state = F.Id("X");
        Formula interfaceType = F.Id("B");
        Formula targetType = F.Id("Y");
        Formula interfaceReadout = F.Id("q");
        Formula target = F.Id("T");
        Formula factor = F.Id("h");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula stateToInterface = Seq(state, Sp, To, Sp, interfaceType);
        Formula stateToTarget = Seq(state, Sp, To, Sp, targetType);
        Formula interfaceRange = Call("range", interfaceReadout);
        Formula targetRange = Call("range", target);
        Formula uniqueFactor = Seq(
            Exists, Bang, Sp, factor, Colon, Sp,
            interfaceRange, Sp, To, Sp, targetRange, Comma, RowBreak, Grp(),
            Call("rangeFactorization", target), Sp, Eq, Sp,
            factor, Sp, Circ, Sp, Call("rangeFactorization", interfaceReadout));
        Formula statement = Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, interfaceType, Comma, Sp, targetType,
            Colon, Sp, type, Comma, RowBreak, Grp(),
            interfaceReadout, Colon, Sp, stateToInterface, Comma, Sp,
            target, Colon, Sp, stateToTarget, Comma, RowBreak, Grp(),
            Call("Injective", interfaceReadout), Sp, Rightarrow, RowBreak, Grp(),
            uniqueFactor, Dot,
            End, Grp(F.Id("gathered"))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "An injective interface uniquely factors every target on its realized image.",
            H("Injective Interface Target Factorization"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("injective-interface-factors-every-target"),
                    DeclarationHandle.Create(
                        "D5/S3/ConceptDynamics/RefinementFactorization/"
                            + "InjectiveInterfaceTargetFactorization."
                            + "injective_interface_factors_every_target"),
                    H("An injective interface factors every target"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Both the interface and target are restricted canonically to "
                                + "their realized images. Thus the factor is total without "
                                + "choosing arbitrary values outside the interface image, and "
                                + "the statement remains valid for an empty state type.")),
                        Paragraph(Text(
                            "Injectivity makes equality of interface values imply equality of "
                                + "states and hence equality of every target value. The imported "
                                + "realized-image kernel criterion turns this kernel inclusion "
                                + "directly into the displayed unique commuting factor."))),
                    DescribeRole.Theorem))));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
