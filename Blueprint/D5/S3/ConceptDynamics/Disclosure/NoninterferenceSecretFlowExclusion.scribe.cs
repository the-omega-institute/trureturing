using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Disclosure;

internal sealed class NoninterferenceSecretFlowExclusionDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Disclosure/NoninterferenceSecretFlowExclusion."
            + "noninterference_secret_flow_exclusion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deterministic noninterference excludes secret-dependent changes in the public "
            + "output of a program flow.",
        H("Noninterference Excludes Secret Flow"),
        Blocks(Describe.Lean(
            DescribeId.Create("noninterference-excludes-secret-dependent-public-output"),
            DeclarationHandle.Create(Declaration),
            H("Secret differences cannot change the public output under noninterference"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Noninterference makes the public output after the program flow a "
                        + "postprocessing of the low-security input. Equal low inputs therefore "
                        + "force equal public outputs.")),
                Paragraph(Text(
                    "A forbidden witness would have equal low inputs and unequal public "
                        + "outputs, alongside the source's explicit unequal-secret clause. "
                        + "Applying noninterference to its low-input equality contradicts the "
                        + "output inequality."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula lowType = F.Id("L");
        Formula highType = F.Id("H");
        Formula programType = F.Id("Y");
        Formula outputType = F.Id("B");
        Formula low = F.Id("l");
        Formula high = F.Id("h");
        Formula flow = F.Id("F");
        Formula output = F.Id("O");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula publicAt(Formula value) => Apply(output, Apply(flow, value));
        Formula sameLow = Equal(Apply(low, left), Apply(low, right));
        Formula differentHigh = new Formula.Not(Equal(Apply(high, left), Apply(high, right)));
        Formula differentOutput = new Formula.Not(Equal(publicAt(left), publicAt(right)));
        Formula publicReadout = Seq(output, Sp, Circ, Sp, flow);
        Formula forbiddenWitness = Seq(
            Exists, Sp, left, Comma, Sp, right, Colon, Sp, state, Comma, Sp,
            sameLow, Sp, Land, Sp, differentHigh, Sp, Land, Sp, differentOutput);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, state, Comma, Sp, lowType, Comma, Sp, highType,
                Comma, Sp, programType, Comma, Sp, outputType, Colon, Sp, type,
                Comma),
            Seq(
                low, Colon, Sp, state, Sp, To, Sp, lowType, Comma, Sp,
                high, Colon, Sp, state, Sp, To, Sp, highType, Comma),
            Seq(
                flow, Colon, Sp, state, Sp, To, Sp, programType, Comma, Sp,
                output, Colon, Sp, programType, Sp, To, Sp, outputType, Comma),
            Seq(
                Call("Refines", publicReadout, low), Sp, Rightarrow, Sp,
                Neg, Sp, Open, forbiddenWitness, Close, Dot),
        ]));
    }
}
