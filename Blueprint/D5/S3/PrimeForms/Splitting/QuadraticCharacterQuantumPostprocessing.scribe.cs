using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.Splitting;

internal sealed class QuadraticCharacterQuantumPostprocessingDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/PrimeForms/Splitting/QuadraticCharacterQuantumPostprocessing."
            + "quadratic_character_quantum_postprocessing_no_go";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three-ring fibers remain indistinguishable under character processing and quantum preparation.",
        H("Quadratic Character Quantum Postprocessing"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("quadratic-character-quantum-postprocessing-no-go"),
                DeclarationHandle.Create(Declaration),
                H("Character processing cannot split a three-ring fiber"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The public input is the canonical three-ring image of units modulo "
                            + "sixty. Equal images force equal Gaussian, Eisenstein, and golden "
                            + "splitting characters, as well as every quadratic character.")),
                    Paragraph(Text(
                        "The classical postprocessor is an arbitrary function of the entire "
                            + "three-coordinate output, so it includes addition, multiplication, "
                            + "and functional calculus wherever those operations are available.")),
                    Paragraph(Text(
                        "Quantum preparation is constructed only from that processed classical "
                            + "value. Applying any final observation therefore gives the same "
                            + "result on both members of the fiber."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula Apply(Formula function, params Formula[] arguments) =>
            new Formula.Apply(function, [.. arguments]);
        Formula unit = F.Id("u"), other = F.Id("v");
        Formula unitType = Call("Units", Call("ZMod", D(6, 0)));
        Formula image = F.Id("triRingImage");
        Formula profile = Apply(image, unit);
        Formula otherProfile = Apply(image, other);
        Formula gaussian = F.Id("gaussianCharacter");
        Formula eisenstein = F.Id("eisensteinCharacter");
        Formula golden = F.Id("goldenCharacter");
        Formula extra = F.Id("chi");
        Formula observerType = Call("QuadraticObserver", unitType);
        Formula classicalType = F.Id("C");
        Formula quantumType = F.Id("Q");
        Formula observationType = F.Id("O");
        Formula process = F.Id("f");
        Formula prepare = F.Id("P");
        Formula observe = F.Id("R");
        Formula processed(Formula value) => Apply(observe, Apply(prepare, Apply(process, value)));

        return Disp(Seq(
            Forall, Sp, unit, Comma, Sp, other, Colon, Sp, unitType, Comma, Sp,
            profile, Sp, Eq, Sp, otherProfile, Sp, Rightarrow, RowBreak, Grp(),
            Apply(gaussian, unit), Sp, Eq, Sp, Apply(gaussian, other), Sp, Land, RowBreak, Grp(),
            Apply(eisenstein, unit), Sp, Eq, Sp, Apply(eisenstein, other), Sp, Land, RowBreak, Grp(),
            Apply(golden, unit), Sp, Eq, Sp, Apply(golden, other), Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, extra, Colon, Sp, observerType, Comma, Sp,
            Apply(extra, unit), Sp, Eq, Sp, Apply(extra, other), Close, Sp, Land, RowBreak, Grp(),
            Forall, Sp, classicalType, Comma, Sp, quantumType, Comma, Sp,
            observationType, Colon, Sp, F.Id("Type"), Comma, Sp,
            process, Colon, Sp, Call("Function", F.Id("ThreeRingProfile"), classicalType), Comma,
            RowBreak, Grp(),
            prepare, Colon, Sp, Call("Function", classicalType, quantumType), Comma, Sp,
            observe, Colon, Sp, Call("Function", quantumType, observationType), Comma,
            RowBreak, Grp(),
            processed(profile), Sp, Eq, Sp, processed(otherProfile), Dot));
    }
}
