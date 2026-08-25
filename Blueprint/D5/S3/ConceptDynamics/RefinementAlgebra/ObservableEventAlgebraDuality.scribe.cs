using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.RefinementAlgebra;

internal sealed class ObservableEventAlgebraDualityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Realized-image refinement is dual to kernels and observable event algebras.",
        H("Refinement and Observable Event Algebras"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("observable-event-algebra-duality"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/RefinementAlgebra/"
                        + "ObservableEventAlgebraDuality.observable_event_algebra_duality"),
                H("Refinement, kernels, and event algebras are equivalent"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "An observable event is a subset of the state carrier whose membership "
                            + "is constant on every fiber of the readout. This is the source's "
                            + "event carrier, rather than a replacement by Boolean-valued maps.")),
                    Paragraph(Text(
                        "Both readouts are normalized to their realized images before the "
                            + "factorization relation is tested. The existing effective-image "
                            + "criterion identifies that factorization with reverse inclusion "
                            + "of their equality kernels.")),
                    Paragraph(Text(
                        "Reverse kernel inclusion transports every fiber-constant event from the "
                            + "coarser readout to the finer one. Conversely, the fiber containing "
                            + "one selected readout value is an observable event that separates "
                            + "any pair the coarser readout distinguishes.")),
                    Paragraph(Text(
                        "Repository searches found no event-algebra definition on the exact set "
                            + "carrier. The adjacent Boolean-question algebra has a different "
                            + "carrier, while the imported kernel theorem supplies the first "
                            + "equivalence directly."))),
                DescribeRole.Theorem))));

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

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula coarseCoordinate = F.Id("O");
        Formula fineCoordinate = F.Id("P");
        Formula coarse = F.Id("q");
        Formula fine = F.Id("r");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula coarseRealized = Call("rangeFactorization", coarse);
        Formula fineRealized = Call("rangeFactorization", fine);
        Formula kernelInclusion = Seq(
            Call("ker", fine), Sp, Subseteq, Sp, Call("ker", coarse));
        Formula refinementKernel = Seq(
            Call("Refines", coarseRealized, fineRealized), Sp, Iff, Sp,
            kernelInclusion);
        Formula algebraInclusion = Seq(
            Call("observableEventAlgebra", coarse), Sp, Subseteq, Sp,
            Call("observableEventAlgebra", fine));

        return Disp(Seq(
            Forall, Sp, state, Comma, Sp, coarseCoordinate, Comma, Sp,
            fineCoordinate, Colon, Sp, type, Comma, RowBreak, Grp(),
            coarse, Colon, Sp, state, Sp, To, Sp, coarseCoordinate, Comma, Sp,
            fine, Colon, Sp, state, Sp, To, Sp, fineCoordinate, Comma,
            RowBreak, Grp(),
            Open, refinementKernel, Close, Sp, Land, RowBreak, Grp(),
            Open, kernelInclusion, Sp, Iff, Sp, algebraInclusion, Close, Dot));
    }
}
