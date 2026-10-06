using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DataProcessing;

internal sealed class FiniteTowerProbabilityExtensionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compatible finite probability laws extend uniquely to the actual threads of an arbitrary total tower.",
        H("Probability Extension Without Surjective Carrier Bonds"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-tower-probability-extension"),
            DeclarationHandle.Create(
                "D5/S3/Estimation/DataProcessing/FiniteTowerProbabilityExtension.exists_unique_extension"),
            H("The original compatible laws have one Borel extension"),
            StatementSource.FromAuthor(
                FormulaDsl.Disp(FormulaDsl.Seq(
                    FormulaDsl.Exists, FormulaDsl.Bang, FormulaDsl.Mu,
                    FormulaDsl.InMacro, Call("Prob", Call("Thread", Id("B"), Id("q"))),
                    FormulaDsl.Comma, FormulaDsl.Forall, FormulaDsl.Sp, Id("l"), FormulaDsl.Comma,
                    Equal(Call("project", FormulaDsl.Mu, Id("l")), Call("theta", Id("l")))))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The statement display is an authored summary under the hypotheses below. "
                        + "Automatic Lean statement projection is unavailable for this declaration "
                        + "in the current projector. The complete constraints, costs and conclusions "
                        + "are specified in the following narrative.")),
                Paragraph(Text(
                    "For every natural level l, B_l is finite and nonempty, with the discrete topology "
                        + "and its Borel measurable structure. The bonding function q_l maps B_(l+1) "
                        + "to B_l and is defined everywhere. It need not be surjective.")),
                Paragraph(Text(
                    "Thread B q is the actual subtype of sequences x with q_l(x_(l+1))=x_l at every "
                        + "level. Its measurable structure is the Borel structure inherited from the "
                        + "countable product of finite discrete spaces. No symbol is removed from B_l.")),
                Paragraph(Text(
                    "The input theta_l is a probability measure on B_l, with exact pushforward "
                        + "compatibility along q_l. Probabilities may have arbitrary real masses and "
                        + "may assign zero mass to symbols. The conclusion supplies a unique probability "
                        + "mu on Thread B q whose l-th coordinate pushforward is theta_l for every l.")),
                Paragraph(Text(
                    "The construction places each finite law on its compatible finite prefix inside "
                        + "the full prefix alphabet. Dropping the last prefix coordinate is surjective. "
                        + "The existing surjective-tower theorem supplies the auxiliary probability."),
                    Ref("D5/S3/Estimation/DataProcessing/InverseLimitProbabilityExtension.exists_unique_probability_extension")),
                Paragraph(Text(
                    "Each auxiliary prefix has full measure in the image of its compatible-prefix "
                        + "embedding. The countable intersection of these full-measure constraints "
                        + "concentrates the decoded product law on the original thread equations. "
                        + "Restriction through the measurable subtype embedding returns the original "
                        + "thread probability, with the required coordinate laws.")),
                Paragraph(Text(
                    "Equal coordinate laws force zero full-event total variation, hence equality of "
                        + "the two probabilities on every measurable event. The event-TV supplier "
                        + "does not require surjective original bonds."),
                    Ref("D5/S3/Estimation/DataProcessing/InverseLimitEventTotalVariation.total_variation_eq_iSup_level")),
                Paragraph(Text(
                    "Uniqueness applies to the extension of the prescribed compatible family. "
                        + "It does not say that every prescribed single-level law extends, or that "
                        + "a nearest feasible law is unique. Only the declared Borel thread event "
                        + "domain is asserted; no arbitrary enlargement is included."))),
            DescribeRole.Theorem))));
}
