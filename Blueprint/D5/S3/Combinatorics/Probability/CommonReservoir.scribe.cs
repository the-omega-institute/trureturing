using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Probability;

internal sealed class CommonReservoirDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Probability/CommonReservoir.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One vertex-and-literal-colour product law satisfies five simultaneous graph reservoir events.",
        H("The common reservoir probability block"),
        Blocks(
            Paragraph(Text("Let G be a loopless directed graph on finite V, coloured properly separately in each direction. Write n=card(V), t=p^3 nu n, Tb=3t/100+5/nu and Tr=t/50+20/nu. Fix L:V to Fin n to finite subsets of V before sampling. Every event uses the same outcome in the Bernoulli-p product on tagged vertex and literal-colour coordinates.")),
            Paragraph(Text("CommonEvent is the conjunction of five assertions: the vertex count is at most 2pn; every outgoing and incoming star retains at least (1-3p) times its actual degree outside both reservoirs; for every u and every w outside its actual repeated-colour exception set B_u with at least nu n/4 two-edge choices, at least Tb actual rainbow choices select their middle vertex and both colours; for every u,i,w whose incoming predecessor set in L(u,i) has size at least nu n/4, at least Tr predecessors select vertex and edge colour; and every vertex has at least Tr such selected incoming neighbours.")),
            Describe.Lean(DescribeId.Create("common-exponential"), DeclarationHandle.Create(Prefix + "common_event_exponential_bound"),
                H("Five failure estimates"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume p in [0,1], nu>0, n>0, both semidegrees at least alpha n, t<=p^2 nu n, t<=p^2 alpha n, Tb<3t/64 and Tr<t/8. Then the probability of CommonEvent is at least one minus the sum exp(-pn/3)+2n exp(-p alpha n/5)+n^2 exp(-9t/512)+n^3 exp(-t/32)+n exp(-t/8). The five terms control size, degrees, rainbow bases, fixed predecessors and incoming neighbours respectively. All failure events are united in one space; no independence between different stars or these five events is required."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("common-five-over-n"), DeclarationHandle.Create(Prefix + "common_reservoir_probability"),
                H("The bound 1-5/n"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For finite V,C require 0<p<=1, 0<nu<1/2, nu<=alpha, n>=64, log n>3, p^3 nu^2 n>=144 log n, and both semidegrees at least alpha n. For every fixed deterministic L as above, the probability of CommonEvent is at least 1-5/n. The scale inequality gives t>=288 log n and the strict threshold inequalities. The five exponential failure terms sum to at most 5/n.")),
                    Paragraph(Text("The numerical hypotheses nu<1/2, n>=64 and log n>3 are explicit in this probability theorem. Their derivation from the original robust-expander hypotheses, the choice of robust layers, and the deterministic construction of paths avoiding all forbidden sets remain separate mathematical steps. This theorem alone does not assert the full connecting lemma."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("literal-equality"), DeclarationHandle.Create(Prefix + "palette_colour_eq_iff"),
                H("Literal colour equality"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any global colour type, restrict to the subtype of literal colours that occur on actual edges. Give nonedges an arbitrary default in this palette. For any two actual edges, equality of the resulting palette colours is equivalent to equality of their original literal colours. The palette is finite because the vertex set is finite."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-palette"), DeclarationHandle.Create(Prefix + "actual_palette_common_reservoir"),
                H("An arbitrary global colour type"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the same graph, parameter, semidegree and fixed-layer assumptions as the bound 1-5/n, the global colour type need not be finite. There exists a palette default such that the product law on V plus the actual finite palette gives CommonEvent probability at least 1-5/n. Positive semidegree supplies that default. Separate properness transfers through literal equality. The sum tags keep vertices and colours independent even when their original types coincide. The estimates are classical Chernoff bounds."))), DescribeRole.Theorem))));
}
