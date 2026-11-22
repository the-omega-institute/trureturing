using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns.Separable;

internal sealed class EndpointPredictableHazardDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual endpoint-cycle hits have a strict-past hazard, whose almost-sure divergence forces recurrent hits.",
        H("Strict-past endpoint hazard and recurrence"),
        Blocks(
            Paragraph(Text("Fix an integer initial offset e and write A(k,e) for the event that actual marked cycle k hits at the offset obtained by adding the first k discrepancy advances to e. The strict past at k contains exactly those k completed marks. For each strict-past measurable set S, M(S,k,e) is the stream mass of S intersected with A(k,e), and I(S,k,e) is the nonnegative integral on S of the next-cycle hazard at that incoming offset.")),
            Describe.Lean(
                DescribeId.Create("actual-predictable-hazard-and-recurrence"),
                DeclarationHandle.Create("D5/S1/Words/Patterns/Separable/EndpointPredictableHazard.actual_predictable_hazard_and_recurrence"),
                H("Conditional probability identity and arbitrarily late shifted hits"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open, Forall, Sp, F.Id("k"), Comma, F.Id("S"), Comma, Sp,
                    Call("Past", F.Id("S"), F.Id("k")), Rightarrow,
                    new Formula.Relation(Call("M", F.Id("S"), F.Id("k"), F.Id("e")),
                        FormulaRelationOperator.Equal, Call("I", F.Id("S"), F.Id("k"), F.Id("e"))),
                    Close, Sp, Land, Sp, Open, Call("D", F.Id("e")), Rightarrow,
                    Call("R", F.Id("e")), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Here D(e) denotes almost-sure divergence of the sum of actual next-cycle hazards. R(e) means that almost surely, for every natural-number threshold N there is a cycle k at or after N in A(k,e). The testing identity is unconditional; only the recurrence implication uses D(e).")),
                    Paragraph(Text("An exact prefix box fixes the incoming offset and factors from the next marked coordinate. The disjoint countable partition of a past event into such boxes gives the test identity. The hazard is bounded by one and is measurable in the strict past, so the nonnegative integral identity identifies its real value with the real conditional expectation of the next hit indicator.")),
                    Paragraph(Text("The hit at k is measurable after revealing mark k, namely at filtration stage k+1. With an empty stage-zero event, Lévy's generalized Borel–Cantelli theorem therefore uses the hazard at stage k, not the filtration that already contains the upcoming mark. The conclusion assumes no independence of hit events and does not assert a finite-permutation limit or unconditional divergence."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
