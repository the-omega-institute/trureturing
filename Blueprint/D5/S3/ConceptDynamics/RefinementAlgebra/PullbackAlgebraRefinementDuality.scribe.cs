using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.RefinementAlgebra;

internal sealed class PullbackAlgebraRefinementDualityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Realized-image refinement is dual to kernels and the canonical pullback algebra.",
        H("Refinement and the Pullback Algebra"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pullback-algebra-refinement-duality"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/RefinementAlgebra/"
                        + "PullbackAlgebraRefinementDuality."
                        + "pullback_algebra_refinement_duality"),
                H("Refinement, kernels, and pullback algebras are equivalent"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The pullback algebra is the repository's canonical family of "
                            + "proposition-valued observables that factor through a readout.")),
                    Paragraph(Text(
                        "Both readouts are normalized to their realized images before "
                            + "factorization is tested. The effective-image kernel theorem "
                            + "supplies the first equivalence.")),
                    Paragraph(Text(
                        "Reverse kernel inclusion transports every observable from the "
                            + "coarser readout to the finer one. Conversely, equality with "
                            + "one selected coarse readout value constructs an observable "
                            + "that separates any pair distinguished by the coarse readout.")),
                    Paragraph(Text(
                        "Body-shape search found the pullback-algebra owner in the imported "
                            + "deterministic-interface module. No duplicate event-algebra "
                            + "definition is introduced here."))),
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
            Call("PullbackAlgebra", coarse), Sp, Subseteq, Sp,
            Call("PullbackAlgebra", fine));

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
