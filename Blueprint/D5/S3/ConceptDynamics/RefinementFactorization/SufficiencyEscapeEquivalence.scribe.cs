using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.RefinementFactorization;

internal sealed class SufficiencyEscapeEquivalenceDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/RefinementFactorization/"
            + "SufficiencyEscapeEquivalence."
            + "sufficiency_escape_equivalence_tfae";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A target has no escape exactly when it is constant on readout fibers and descends to the realized image.",
        H("Sufficiency-Escape Equivalence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sufficiency-escape-equivalence"),
                DeclarationHandle.Create(Declaration),
                H("Four sufficient target conditions are equivalent"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The theorem uses the repository's canonical defectRelation and "
                            + "Setoid kernel. Fiber constancy is the pinned FactorsThrough "
                            + "predicate.")),
                    Paragraph(Text(
                        "The descending map is defined only on the realized range of q. "
                            + "No inhabitance assumption or extension to the whole coordinate "
                            + "codomain is present."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula coordinate = F.Id("C");
        Formula targetType = F.Id("Y");
        Formula readout = F.Id("q");
        Formula target = F.Id("T");
        Formula descend = F.Id("Tbar");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));

        Formula emptyEscape = Seq(
            Call("defectRelation", readout, target), Sp, Eq, Sp, Emptyset);
        Formula kernelInclusion = Seq(
            Call("ker", readout), Sp, Subseteq, Sp, Call("ker", target));
        Formula fiberConstancy = Call("FactorsThrough", target, readout);
        Formula imageDescent = Seq(
            Exists, Sp, descend, Colon, Sp,
            Call("range", readout), Sp, To, Sp, targetType, Comma, Sp,
            target, Sp, Eq, Sp, descend, Sp, Circ, Sp,
            Call("rangeFactorization", readout));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, coordinate, Comma, Sp, targetType,
            Colon, Sp, type, Comma, RowBreak, Grp(),
            readout, Colon, Sp, state, Sp, To, Sp, coordinate, Comma, Sp,
            target, Colon, Sp, state, Sp, To, Sp, targetType, Comma,
            RowBreak, Grp(),
            Call("ListTFAE", Grp(OpenBracket,
                emptyEscape, Comma, Sp,
                kernelInclusion, Comma, Sp,
                fiberConstancy, Comma, Sp,
                imageDescent,
                CloseBracket)), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
