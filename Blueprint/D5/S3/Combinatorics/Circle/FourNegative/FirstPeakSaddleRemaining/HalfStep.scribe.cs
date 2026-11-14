using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleRemaining;

internal sealed class HalfStepDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Half-step interpolation and native selection",
        H("The c>=3, a>c+d region"),
        Blocks(
            Describe.Lean(DescribeId.Create("helper-half-step-1"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleRemaining/HalfStep.half_interpolate"),
                H("Interpolate in r and then h"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("HalfCorners contains one negative corner, four positive rectangle corners and the boundary case. The three certificate modules cover K>=4, F>=4 or K,F>=2. half_interpolate uses the explicit separate affine identities in r and h, with no hr term; half_floor_split chooses a positive r even at exact multiples."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("helper-half-step-2"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleRemaining/HalfStep.half_step_choice_exists"),
                H("Construct masks above the diagonal"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a>b>d>c>=3, a>c+d and b<=c+d, set K=2^(b-d-1), F=2^(c+d-b), e=2^(a-c-d-1), so z=2KF and J=Fe. Dyadic parameter cases select one of the three certificate regions. half_arithmetic assembles the residue choice and margins, then native_of_selection gives NativeChoice. No extra grain restriction is a theorem hypothesis."))), DescribeRole.Lemma),
            Paragraph(Text("These existing private declarations are consumed by the strict-saddle endpoint. This mirror documents their stated hypotheses and use; it makes no independent literature-novelty claim, no claim of a four-slot registration for every helper, and no claim to settle unrestricted four-gap J or Circle Conjecture 3.1."))), []));
}
