using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeUniformPlanDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPlan.";
    private static DocumentBlock Entry(string n, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("nativeuniformplan-" + n.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + n), H(n), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeUniformPlan", H("NativeUniformPlan"), Blocks(
            Paragraph(Text("Finite singleton-equation native plans preserve the required branch order: native failure, collapse of any old disequality under the fully composed action, all actual bound variables ground, and feasible nonground action. Empty bound domains pass groundness vacuously. The original solver is reused. Presentation transport preserves its exact native input and deterministic output.")),
            Entry("templateWord", "Serialize a finite ordinal term after replacing residual variables by the fixed Boolean test leaf.", DescribeRole.Definition),
            Entry("kindCode", "The four native branches are encoded as zero for failure, one for old collapse, two for ground bindings and three for feasible nonground action.", DescribeRole.Definition),
            Entry("codePlan", "Preserve both addresses, the native branch and the ordered finite-domain binding list. Each ground source retains its complete constructor word.", DescribeRole.Definition),
            Entry("codedPlan", "Unify the singleton new equality. Test every old disequality under the normalized returned action before testing groundness of the actual bound domain. Identity outside that domain stays free; an empty domain passes the ground test vacuously.", DescribeRole.Definition),
            Entry("coded_plan_computable", "The fixed finite input algorithm is computable. The proof uses the existing uniform native solver and primitive checks of the fully composed action; it does not assume that unification is primitive recursive.", DescribeRole.Theorem),
            Entry("coded_plan_exact", "For every finite ordinal presentation and every complete old-disequality list, the computed code equals the original native singleton-equation pair plan, including branch order and ground bindings.", DescribeRole.Theorem),
            Entry("renameTerm", "Rename residual variables while retaining Boolean constructors and the exact ordered binary tree.", DescribeRole.Definition),
            Entry("ordinalPlan", "Serialize a variable-indexed native pair plan through the supplied ordinal map, retaining both addresses, branch and every binding template.", DescribeRole.Definition),
            Entry("plan_transport", "Transport a presentation along an equivalence while preserving the exact underlying native String input. The original solver therefore chooses the same native result; arbitrary-renaming invariance of a chosen MGU is not assumed.", DescribeRole.Theorem))));
}
