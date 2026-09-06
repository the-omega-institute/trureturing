using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class ExplicitLargeHeightZeroCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/ZetaBridge/ExplicitLargeHeightZeroCount.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A numerical large-height window bound for actual zeta zeros, derived from the existing explicit zeta-growth and Jensen theorems.",
        H("Explicit Large-Height Zero Count"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("explicit-large-height-half-count"),
                DeclarationHandle.Create(Prefix + "half_count_large_explicit"),
                H("Retain the actual constants in the Jensen disk proof"),
                StatementSource.FromAuthor(Disp(F.Id("For every real t with |t|>=4, NhalfR(t)<=64 log(|t|+3)."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Adapt the existing LocalCount disk argument with its actual growth bound C=20/3 and A=1. The disks retain radii 0.84 and 0.95; their logarithmic ratio is at least 11/95. Bound log(20) by 5. The proof uses actual analytic multiplicities and never obtains an unspecified growth constant or a small-height zero count. The geometric proof follows the Apache-2.0 Zeta23 port identified in the Lean source; no novelty or optimality is claimed for the coefficient 64."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("explicit-large-height-full-count"),
                DeclarationHandle.Create(Prefix + "zetaZeroConfig_large_count_explicit"),
                H("Count the actual full critical-strip window"),
                StatementSource.FromAuthor(Disp(F.Id("For |t|>=4, zetaZeroConfig.N(t,t+1)<=128 log(|t|+3)."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Reuse the existing same-height reflection halving bound. Zeros on the critical line and their analytic multiplicities are treated by that owner. The interval convention is (t,t+1]. No RH hypothesis, numerical root certificate, or bound at small heights is required. This is a Candidate proof source; compilation and axiom closure are separate evidence."))),
                DescribeRole.Theorem)), []));
}
