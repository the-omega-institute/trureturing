using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.TestFunctions;

internal sealed class LocalPositiveSpectrumCompletionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/TestFunctions/LocalPositiveSpectrumCompletion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local positive definiteness is equivalent to positive spectral completion modulo the "
            + "fixed window's invisible distributions.",
        H("Local Positive-Spectrum Completion"),
        Blocks(
            DefinitionNode(
                "well-posed",
                "WellPosed",
                "Local well-posedness",
                "Every test visible in the fixed local window has nonnegative source reading."),
            DefinitionNode(
                "has-positive-extension",
                "HasPositiveExtension",
                "Positive spectral extension",
                "A positive tempered spectrum has inverse Fourier transform differing from the "
                    + "source by an element of the window kernel."),
            DefinitionNode(
                "has-positive-correction",
                "HasPositiveCorrection",
                "Positive external correction",
                "Adding a window-invisible correction makes the Fourier spectrum positive."),
            Describe.Lean(
                DescribeId.Create("local-positive-spectrum-completion"),
                DeclarationHandle.Create(Prefix + "local_positive_spectrum_completion"),
                H("Local positive-spectrum completion"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The source theorem is conditional on the standard finite-order tempered "
                            + "positive-definite extension theorem. Since pinned Mathlib has no "
                            + "such theorem, the formal statement exposes exactly its constructive "
                            + "local-to-global direction as a hypothesis.")),
                    Paragraph(Text(
                        "The reverse implication is not assumed: a positive spectrum gives "
                            + "nonnegative local readings through the inverse-Fourier pairing and "
                            + "vanishing of every window-kernel correction.")),
                    Paragraph(Text(
                        "For the final equivalence, an extension spectrum constructs the explicit "
                            + "correction F inverse of nu minus W. Conversely, a correction kappa "
                            + "constructs the explicit spectrum F of W plus kappa."))),
                DescribeRole.Theorem))));

    private static DocumentBlock.Describe DefinitionNode(
        string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(heading),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            DescribeRole.Definition);

    private static Formula TheoremFormula()
    {
        Formula distribution = F.Id("D");
        Formula spectrum = F.Id("S");
        Formula test = F.Id("T");
        Formula fourier = F.Id("F");
        Formula reading = F.Id("r");
        Formula energy = F.Id("E");
        Formula positive = F.Id("P");
        Formula kernel = F.Id("K");
        Formula source = F.Id("W");
        Formula nu = F.Id("nu");
        Formula kappa = F.Id("kappa");
        Formula f = F.Id("f");
        Formula inverse(Formula value) => Call("inverse", fourier, value);
        Formula reads(Formula value, Formula probe) => Apply(reading, value, probe);
        Formula positiveAt(Formula value) => Apply(positive, value);
        Formula energyAt(Formula value, Formula probe) => Apply(energy, value, probe);
        Formula inKernel(Formula value) => Seq(value, Sp, InMacro, Sp, kernel);
        Formula wellPosed = Call("WellPosed", reading, source);
        Formula extension = Exists(
            nu,
            Seq(positiveAt(nu), Sp, Land, Sp,
                inKernel(Seq(inverse(nu), Sp, Minus, Sp, source))));
        Formula correction = Exists(
            kappa,
            Seq(inKernel(kappa), Sp, Land, Sp,
                positiveAt(Apply(fourier, Seq(source, Sp, Plus, Sp, kappa)))));
        Formula pairingLaw = Seq(
            Forall, Sp, nu, Comma, Sp, f, Comma, Sp,
            reads(inverse(nu), f), Sp, Eq, Sp, energyAt(nu, f));
        Formula positiveEnergy = Seq(
            Forall, Sp, nu, Comma, Sp,
            positiveAt(nu), Sp, Rightarrow, Sp,
            Forall, Sp, f, Comma, Sp, D(0), Sp, Leq, Sp, energyAt(nu, f));
        Formula invisibleReading = Seq(
            Forall, Sp, kappa, Comma, Sp,
            inKernel(kappa), Sp, Rightarrow, Sp,
            Forall, Sp, f, Comma, Sp, reads(kappa, f), Sp, Eq, Sp, D(0));
        Formula extensionHypothesis = Seq(wellPosed, Sp, Rightarrow, Sp, extension);

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, distribution, Comma, Sp, spectrum, Comma, Sp, test, Comma),
            Seq(fourier, Colon, Sp, Call("AddEquiv", distribution, spectrum), Comma, Sp,
                reading, Colon, Sp, Call("AddHom", distribution, Call("Function", test, Call("Real"))),
                Comma),
            Seq(energy, Colon, Sp, Call("Function", spectrum, test, Call("Real")), Comma, Sp,
                positive, Colon, Sp, Call("Predicate", spectrum), Comma),
            Seq(kernel, Colon, Sp, Call("AddSubgroup", distribution), Comma, Sp,
                source, Colon, Sp, distribution, Comma),
            Seq(pairingLaw, Comma),
            Seq(positiveEnergy, Comma),
            Seq(invisibleReading, Comma),
            Seq(Grp(extensionHypothesis), Sp, Rightarrow),
            Seq(Open, wellPosed, Sp, Iff, Sp, extension, Close, Sp, Land),
            Seq(Open, extension, Sp, Iff, Sp, correction, Close, Dot),
        ]));
    }

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Exists(Formula variable, Formula body) =>
        Seq(F.Exists, Sp, variable, Comma, Sp, body);
}
