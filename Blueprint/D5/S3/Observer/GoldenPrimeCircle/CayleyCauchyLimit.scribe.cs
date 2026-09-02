using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenPrimeCircle;

internal sealed class CayleyCauchyLimitDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/GoldenPrimeCircle/CayleyCauchyLimit.cayley_cauchy_limit";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform finite cyclic phases converge weakly under the Cayley chart to the "
            + "standard Cauchy probability measure.",
        H("Cayley-Cauchy Limit"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cayley-cauchy-limit"),
                DeclarationHandle.Create(Declaration),
                H("Finite cyclic Haar phases have the standard Cauchy limit"),
                StatementSource.FromAuthor(Disp(Call("Tendsto",
                    F.Id("cayleyCauchyEmpirical"), F.Id("atTop"),
                    Call("nhds", F.Id("standardCauchyProbabilityMeasure"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For modulus K=n+2, cyclicHaarPhase n is the uniform probability "
                            + "measure on the scaled integral-lattice phases j/K with "
                            + "1 <= j < K. The empirical law is its pushforward by "
                            + "cayleyPhase(u)=tan(pi(u-1/2))=-cot(pi u).")),
                    Paragraph(Text(
                        "As n tends to infinity, these probability measures converge in "
                            + "Mathlib's weak topology to standardCauchyProbabilityMeasure, "
                            + "the canonical cauchyMeasure 0 1 with density "
                            + "dh/(pi(1+h^2)). This is one weak-convergence assertion; the "
                            + "supporting interval counts and CDF identities are not stated "
                            + "as additional conclusions."))),
                DescribeRole.Theorem))));
}
