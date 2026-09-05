using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class WeilFullGramUniformRemainderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/ZetaBridge/WeilFullGramUniformRemainder.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual full Gram has a coefficient-uniform remainder and retains a fixed negative margin and exact inertia at every sufficiently large common depth.",
        H("Eventual Uniform Negativity of the Actual Gram"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-gram-uniform-remainder"),
                DeclarationHandle.Create(Prefix + "burnol_actual_gram_uniform_remainder"),
                H("The full matrix inherits the derived remainder"),
                StatementSource.FromAuthor(Disp(F.Id("abs(Re(a*G_N a)-Q_target(a)) <= 4^(-(N+1)) C E(a)."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Use the existing exact full-Gram quadratic identity and the common Burnol remainder. C is the absolutely summed mixed majorant of the fixed killer family; every cross term is retained."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-gram-eventual-negative-margin"),
                DeclarationHandle.Create(Prefix + "eventually_burnolGram_uniform_negative_margin"),
                H("One threshold for every coefficient and all later depths"),
                StatementSource.FromAuthor(Disp(F.Id("For 0<delta<4, eventually for every a, Re(a*G_N a) <= -(4-delta) E(a)."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Geometric error convergence supplies the common threshold. Positivity of each analytic multiplicity supplies the weight floor one. The quantifiers are uniform over all coefficient vectors and all depths beyond the threshold."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-gram-eventual-exact-inertia"),
                DeclarationHandle.Create(Prefix + "eventually_burnolGram_exact_negative_inertia"),
                H("Exact spectral inertia throughout the tail"),
                StatementSource.FromAuthor(Disp(F.Id("For every sufficiently large N, PosDef(-G_N) and RHLinalg.negIndex(G_N)=card(orbit channels)."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Positive coefficient energy turns the uniform margin into strict negativity. The existing full-Gram inertia theorem supplies the spectral index. A valid finite off-line frame remains an input; its existence and a computable conditioning bound are not asserted."))),
                DescribeRole.Theorem)), []));
}
