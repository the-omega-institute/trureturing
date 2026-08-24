using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Experiment;

internal sealed class InfiniteIdentificationFiniteFailureDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A countable transcript can identify two probability laws almost surely even though "
            + "their coordinate laws are equivalent and no finite prefix admits an exact decoder.",
        H("Infinite Identification without Finite Exact Tomography"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("infinite-identification-not-finite-exact-tomography"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Experiment/InfiniteIdentificationFiniteFailure."
                        + "infinite_identification_not_finite_exact_tomography"),
                H("Almost-sure infinite identification has no finite exact converse"),
                StatementSource.FromAuthor(SeparationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The two states generate independent Boolean product laws with constant "
                            + "success probabilities one third and two thirds. Both Boolean "
                            + "coordinate laws have full support, hence are mutually absolutely "
                            + "continuous.")),
                    Paragraph(Text(
                        "The measurable classifier event consists of transcripts whose empirical "
                            + "means converge to two thirds. The strong law gives probability zero "
                            + "for this event in the lower state and probability one in the upper "
                            + "state.")),
                    Paragraph(Text(
                        "At every finite prefix length, the all-false cylinder has positive mass "
                            + "under both product laws. A decoder that is almost surely correct "
                            + "would therefore have to label that same prefix both false and true.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies Bernoulli laws, product-coordinate independence, "
                            + "the strong law, and convergence-event measurability. The repository's "
                            + "canonical varying-marginal green-class theorem supplies finite-"
                            + "cylinder positivity."))),
                DescribeRole.Theorem))));

    private static Formula SeparationFormula()
    {
        Formula sample = F.Id("x");
        Formula length = F.Id("m");
        Formula decoder = F.Id("d");
        Formula eventFormula = F.Id("distinguishingEvent");
        Formula lowerMarginal = Call("marginal", F.Id("lowerBias"));
        Formula upperMarginal = Call("marginal", F.Id("upperBias"));
        Formula falseLaw = Call("stateLaw", F.Id("false"));
        Formula trueLaw = Call("stateLaw", F.Id("true"));
        Formula falseExact = Call(
            "AE",
            falseLaw,
            Seq(LambdaLower, Sp, sample, Sp, Mapsto, Sp,
                Equal(Call("d", Call("finiteTranscript", length, sample)), F.Id("false"))));
        Formula trueExact = Call(
            "AE",
            trueLaw,
            Seq(LambdaLower, Sp, sample, Sp, Mapsto, Sp,
                Equal(Call("d", Call("finiteTranscript", length, sample)), F.Id("true"))));

        return Disp(new Formula.Aligned([
            Seq(Call("AC", lowerMarginal, upperMarginal), Sp, Land),
            Seq(Call("AC", upperMarginal, lowerMarginal), Sp, Land),
            Seq(Call("Measurable", eventFormula), Sp, Land),
            Seq(Call("Pr", falseLaw, eventFormula), Sp, Eq, Sp, D(0), Sp, Land),
            Seq(Call("Pr", trueLaw, eventFormula), Sp, Eq, Sp, D(1), Sp, Land),
            Seq(
                Neg, Sp, Exists, Sp, length, Colon, Sp,
                Operatorname, Grp(F.Id("Nat")), Comma, Sp,
                decoder, Colon, Sp,
                Open, Call("Fin", length), Sp, To, Sp,
                Operatorname, Grp(F.Id("Bool")), Close,
                Sp, To, Sp, Operatorname, Grp(F.Id("Bool")), Comma, Sp,
                falseExact, Sp, Land, Sp, trueExact, Dot),
        ]));
    }
}
