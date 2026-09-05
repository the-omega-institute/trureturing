using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Chronology;

internal sealed class PrimeGoldenBidegreePhaseSeparationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Chronology/PrimeGoldenBidegreePhaseSeparation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One scalar Euler phase sample can alias bidegrees, while the complete time trajectory recovers the bidegree.",
        H("Prime-Golden Bidegree Phase Separation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-golden-phase-observation-boundary"),
                DeclarationHandle.Create(
                    Prefix + "prime_golden_phase_observation_boundary"),
                H("A snapshot aliases and the complete phase trajectory separates"),
                StatementSource.FromAuthor(ObservationBoundaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At time zero every bidegree has unit phase, giving an explicit noninjective scalar sample.")),
                    Paragraph(Text(
                        "For distinct bidegrees, the half-beat of their nonzero frequency difference sends the relative phase to minus one and separates them.")),
                    Paragraph(Text(
                        "The full scalar trajectory therefore recovers the two count coordinates, while Magnus or Hopf data is still required for event order."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula ObservationBoundaryFormula()
    {
        Formula prime = F.Id("p");
        Formula degree = F.Id("d");
        Formula time = F.Id("t");
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, prime, Colon, Sp, F.Id("Nat"), Dot, F.Id("Primes"), Comma, RowBreak, Grp(),
            Neg, Call("Injective", Seq(degree, Sp, Mapsto, Sp, Call("bidegreePhase", D(0), prime, degree))),
            Sp, Land, RowBreak, Grp(),
            Call("Injective", Seq(degree, Sp, Mapsto, Sp,
                Open, time, Sp, Mapsto, Sp, Call("bidegreePhase", time, prime, degree), Close)), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
