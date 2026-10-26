using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.MutualVisibility;

internal sealed class ConnectivityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/MutualVisibility/Connectivity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/fresanfigueroa2026mutualvisibility");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original-host mutual visibility and the auxiliary geometry of the full mixed reconfiguration graph.",
        H("Separators and reachability in one surviving graph"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("connectivity-le-min-degree"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/MutualVisibility/Connectivity.connectivity_le_minDegree"),
                H("Connectivity is bounded by minimum degree"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every finite nonempty simple graph, the separator connectivity is at most minimum degree."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("min-degree-le-connectivity"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/MutualVisibility/Connectivity.minDegree_le_connectivity"),
                H("All smaller cuts give the reverse inequality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("If deleting every cut smaller than minimum degree leaves a preconnected graph, minimum degree is at most separator connectivity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("full-maximal-connectivity-claim"),
                DeclarationHandle.Create(Prefix + "FullMaximalConnectivityClaim"),
                H("The entire original question"),
                StatementSource.FromAuthor(TargetFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Every finite nonempty simple undirected connected host is quantified, including orders one and two. Its full original-geodesic visibility graph, with empty configurations, every rank, all single-label additions and removals, and all actual-host-edge slides, is asserted to have vertex connectivity equal to minimum degree. The minimum-pair separator argument proves this equality."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cutreach"),
                DeclarationHandle.Create(Prefix + "CutReach"),
                H("Reachability after one fixed deletion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Both endpoints survive the given cut and are joined inside the actual induced graph after deleting that same cut."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cutreach-step"),
                DeclarationHandle.Create(Prefix + "cutReach_step"),
                H("Extending a surviving path"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("A reachable endpoint can be extended across an actual graph edge whenever the next vertex survives the same fixed cut.")))),
            Describe.Lean(
                DescribeId.Create("cutreach-two-step-payment"),
                DeclarationHandle.Create(Prefix + "cutReach_two_step_payment"),
                H("A cut met by a two-edge escape"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("If one vertex is reachable in the surviving component and a two-edge path ends outside it, at least one of the next two vertices belongs to the given cut. Both edges and both payments concern one common graph and cut.")))),
            Describe.Lean(
                DescribeId.Create("cutreach-chain-payment"),
                DeclarationHandle.Create(Prefix + "cutReach_chain_payment"),
                H("A cut met by a finite chain"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Consecutive vertices along the stated finite index interval are adjacent. If its upper endpoint lies in the component or is cut and its lower endpoint lies outside the component, at least one indexed vertex is cut. The proof joins every uncut chain step and contradicts endpoint separation.")))))));

    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula TargetFormula()
    {
        Formula v = F.Id("V"), h = F.Id("H"), r = Call("reconfiguration", h);
        Formula equality = new Formula.Relation(Call("vertexConnectivity", r),
            FormulaRelationOperator.Equal, Call("minDegree", r));
        Formula target = All("V", Call("Type"), Seq(
            OpenBracket, Call("Fintype", v), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", v), CloseBracket, Sp,
            OpenBracket, Call("Nonempty", v), CloseBracket, Sp,
            All("H", Call("SimpleGraph", v), new Formula.Logic(Call("Connected", h),
                FormulaLogicOperator.Implies, equality))));
        return Disp(new Formula.Logic(Call("FullMaximalConnectivityClaim"), FormulaLogicOperator.Iff, target));
    }
}
