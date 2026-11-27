using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.RecordWriting;

internal sealed class TwoRegisterRecordingDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/RecordWriting/TwoRegister.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Entropy/chung2026thermodynamicobjectivity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A sharp bath variation budget for writing two classical records with joint reversible gates.",
        H("Writing two records with local baths and joint permutations"),
        Blocks(
            Theorem("mass-range", "potential_eq_twice_range",
                "The permutation-invariant range",
                "The maximum of the three pairwise sums of absolute Walsh moments equals "
                + "twice the range of the four joint masses. Pairwise mass differences give "
                + "both relative signs for each pair of moments."),
            Theorem("local-bath-variation", "firstBath_potential_le",
                "Variation controls the increase during a local bath",
                "The bath on the first bit preserves the second bit's signed moment. It "
                + "interpolates the parity moment toward the product of that preserved "
                + "moment and the reset bias. This bounds the increase in the potential "
                + "by twice the total variation of the joint law across the contact."),
            Theorem("two-record-contrast", "recording_bound",
                "The two marginal contrasts require bath variation",
                "Both event branches start uniform on the same two-bit register. Each "
                + "branch permits any finite sequence of joint permutations and independent "
                + "single-bit relaxation steps. The sum of the total variation distances "
                + "between the two final single-bit marginals is at most the sum of the "
                + "bath variations in the two branches. Joint permutations preserve the "
                + "range of the masses even when the permutation depends on the event. "
                + "For a uniform event, each marginal distance is one minus twice its "
                + "Bayes decoding error. This is the finite transport step for the "
                + "collective extension posed after Equation (7) in Chung's Section VIII."),
            Theorem("sharp-two-record-contrast", "recording_bound_sharp",
                "Two resets attain the bath variation bound",
                "For any two target contrasts in the unit interval, reset one bit at a time "
                + "to independent laws of those biases. Complement both bits in one event "
                + "branch at the end. The two marginal contrasts equal the prescribed "
                + "values and the two branch variations sum to their sum."))));

    private static DocumentBlock Theorem(
        string id, string name, string title, string prose) => Describe.Lean(
        DescribeId.Create(id),
        DeclarationHandle.Create(Module + name),
        H(title),
        StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))),
        DescribeRole.Theorem);
}
