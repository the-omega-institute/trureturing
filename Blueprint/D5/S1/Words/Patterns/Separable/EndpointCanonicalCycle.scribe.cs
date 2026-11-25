using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns.Separable;

internal sealed class EndpointCanonicalCycleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original emitted coordinates agree with the canonical marked-cycle test on every sufficiently long successful bounded history.",
        H("Canonical cycle parsing and original coordinates"),
        Blocks(
            Paragraph(Text("For an actual permutation avoiding 2413 and 3142, the canonical parser recovers its signed least proper cut. It emits a strictly shorter left factor or removes a strictly shorter right factor, retaining the actual factorization and residual. Ties and unsuccessful recursions do not count as successful parses.")),
            Paragraph(Text("On a successful bounded tuple, erasing the cutoffs retains the same actual marked cycles and remaining permutation. For a fixed number of cycles k, integer target e, and natural bounds K,H, write A(n,pi) for successful canonical parsing followed by the literal test i-pi(i)=e at an emitted position. Q(p) is the recursive erased-tuple hit test at e.")),
            Describe.Lean(
                DescribeId.Create("actual-canonical-first-k-literal-hit-agreement"),
                DeclarationHandle.Create("D5/S1/Words/Patterns/Separable/EndpointCanonicalCycle.actualCanonicalFirstKLiteralHit_eventually_agrees"),
                H("Eventual literal agreement on successful bounded histories"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("Eventually"), Sp, F.Id("n"), Comma, Sp,
                    Forall, Sp, F.Id("p"), Comma, F.Id("pi"), Comma, Sp,
                    new Formula.FunctionCall(FormulaIdentifier.Create("Event"), [F.Id("p"), F.Id("n"), F.Id("pi")]), Sp,
                    F.Id("implies"), Sp,
                    new Formula.FunctionCall(FormulaIdentifier.Create("iff"), [
                        new Formula.FunctionCall(FormulaIdentifier.Create("A"), [F.Id("n"), F.Id("pi")]),
                        new Formula.FunctionCall(FormulaIdentifier.Create("Q"), [F.Id("p")])])))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The residual embedding shifts positions by the emitted count and shifts values by the advance in the lower-value origin. Their difference is the recursively accumulated mark increment. Direct emissions retain the literal local occupancy test. The residual size bound excludes a skew emission at the specified offset, uniformly over the finitely many bounded tuples.")),
                    Paragraph(Text("The result compares the original points only in the emitted prefix. It does not test removed or residual points, assert agreement on parser failures, or make the cutoff uniform in k or e."))),
                DescribeRole.Theorem))));
}
