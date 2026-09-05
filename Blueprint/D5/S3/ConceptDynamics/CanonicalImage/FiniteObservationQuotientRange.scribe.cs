using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.CanonicalImage;

internal sealed class FiniteObservationQuotientRangeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite joint-readout quotient is equivalent to its realized image.",
        H("Finite Observation Quotient Range"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-observation-quotient-is-its-realized-range"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/CanonicalImage/FiniteObservationQuotientRange."
                        + "finite_observation_quotient_equiv_range"),
                H("The finite observation quotient is its realized range"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let X be a state type, I an observation-index type, O a dependent "
                            + "output family, q the corresponding readout family, and J a finite "
                            + "subset of I. FiniteObservationOutput is the dependent product over "
                            + "J, and finiteObservationReadout is the imported jointReadout "
                            + "restricted to indices in J.")),
                    Paragraph(Text(
                        "staticRelativeIdentity is exactly the equality kernel of that finite "
                            + "readout, and EffectiveObservationQuotient is its Setoid quotient. "
                            + "The displayed Nonempty equivalence identifies this named quotient "
                            + "with precisely the Set.range of the same finite readout.")),
                    Paragraph(Text(
                        "Pinned Mathlib and Loogle provide the exact arbitrary-function result "
                            + "Setoid.quotientKerEquivRange. The Lean theorem applies it directly; "
                            + "there is no finiteness condition on X, no injectivity or "
                            + "surjectivity premise, and no claim about the full output type."))),
                DescribeRole.Theorem))));

    private static Formula Apply(string name, params Formula[] arguments)
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

    private static Formula TheoremFormula()
    {
        Formula indexType = F.Id("I");
        Formula stateType = F.Id("X");
        Formula output = F.Id("O");
        Formula readout = F.Id("q");
        Formula budget = F.Id("J");
        Formula index = F.Id("i");
        Formula outputAt = Apply("O", index);
        Formula finiteReadout = Apply("finiteObservationReadout", readout, budget);
        Formula quotient = Apply("EffectiveObservationQuotient", readout, budget);
        Formula realizedRange = Apply("range", finiteReadout);

        return Disp(Seq(
            Forall, Sp, indexType, Comma, Sp, stateType, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Sp,
            output, Colon, Sp, indexType, Sp, To, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Sp,
            readout, Colon, Sp, Forall, Sp, index, Colon, Sp,
            indexType, Comma, Sp, stateType, Sp, To, Sp, outputAt, Comma, Sp,
            budget, Colon, Sp, Apply("Finset", indexType), Comma, Esc,
            Apply("Nonempty", Grp(Seq(
                quotient, Sp, Equiv, Sp, realizedRange))), Dot));
    }
}
