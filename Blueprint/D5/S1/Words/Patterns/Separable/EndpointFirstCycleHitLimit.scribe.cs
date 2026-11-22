using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns.Separable;

internal sealed class EndpointFirstCycleHitLimitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed number of actual emitted cycles has a literal finite diagonal-hit probability converging to the marked-stream law.",
        H("Finite-to-stream convergence of literal diagonal hits"),
        Blocks(
            Paragraph(Text("Fix a natural number k and an integer e. Write p(n) for the uniform mass among size-n avoiders of the event that canonical parsing succeeds through k cycles and some original emitted point satisfies i-pi(i)=e. Write q(k,e) for the first-k hit probability under the actual marked-stream law. Each cycle uses the starting offset plus the lower-value-minus-position advances of the previous cycles.")),
            Describe.Lean(
                DescribeId.Create("actual-canonical-first-k-literal-hit-limit"),
                DeclarationHandle.Create("D5/S1/Words/Patterns/Separable/EndpointFirstCycleHitLimit.actualCanonicalFirstKLiteralHit_limit"),
                H("Full-sequence convergence at fixed k and e"),
                StatementSource.FromAuthor(Disp(
                    new Formula.FunctionCall(FormulaIdentifier.Create("Tendsto"), [
                        F.Id("p"), F.Id("atTop"),
                        new Formula.FunctionCall(FormulaIdentifier.Create("nhds"), [
                            new Formula.FunctionCall(FormulaIdentifier.Create("q"), [F.Id("k"), F.Id("e")])])]))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The bounded successful tuple cells are disjoint and their actual finite probabilities converge to the corresponding stream cylinders. Eventual original-coordinate agreement identifies precisely the selected cells on each side. The same finite family controls the probabilities omitted on both sides; bounding the two complementary masses and the finite-sum error proves convergence over the full sequence.")),
                    Paragraph(Text("The statement fixes k and e before taking n to infinity. It is not a growing-k estimate, an occupied lower-quantile bound, a multi-cycle divergence result, or a theorem about the entire permutation's diagonal."))),
                DescribeRole.Theorem))));
}
