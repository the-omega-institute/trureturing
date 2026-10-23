using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics;

internal sealed class StableRangeDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/StableRange.";
    private static Formula V(string name) => F.Id(name);
    private static Formula All(string name, Formula type) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp);
    private static Formula Inst(string name) =>
        Seq(OpenBracket, Call(name, V("X")), CloseBracket, Sp);
    private static Formula K => Call("core", V("f"));
    private static Formula R => Call("restriction", V("f"));
    private static Formula Statement => Disp(new Formula.Aligned([
        Seq(All("X", Call("Type", V("u"))), Inst("TopologicalSpace"),
            Inst("CompactSpace"), Inst("T2Space")),
        Seq(All("f", Seq(V("X"), Sp, To, Sp, V("X"))),
            Call("Continuous", V("f")), Sp, Rightarrow),
        Seq(Call("IsCompact", K), Sp, Land, Sp, Call("Continuous", R),
            Sp, Land, Sp, Call("Surjective", R))
    ]));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A continuous compact Hausdorff endomorphism restricts to a continuous surjection of its actual compact stable range.",
        H("Compact stable ranges"), Blocks(
            Paragraph(Text("For any self-map f, core(f) is the literal intersection of range(f^n) over every natural n, including zero. "
                + "It is forward invariant without topology: an n-step preimage of c gives an (n+1)-step preimage of f(c). "
                + "restriction(f) sends the actual subtype point c to f(c), with invariance proving subtype membership.")),
            Describe.Lean(DescribeId.Create("compact-onto-stable-restriction"),
                DeclarationHandle.Create(Owner + "compact_surjective_restriction"),
                H("The compact onto core system"), StatementSource.FromAuthor(Statement),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Topology/banaschewski1955nulldimensional")),
                Blocks(
                    Paragraph(Text("Every iterate is continuous. Its range is compact and therefore closed in Hausdorff X. "
                        + "Their intersection is closed; compactness of X gives compactness of this same core.")),
                    Paragraph(Text("Fix c in the core. For each natural n form F(n)=range(f^n) intersected with f inverse-image of {c}. "
                        + "These are closed and decreasing. Membership of c in range(f^(n+1)) gives a point f^n(a) in F(n). "
                        + "The compact nested-intersection theorem supplies one a in every F(n). It lies in the actual core and satisfies f(a)=c. "
                        + "This proves surjectivity of the actual restriction, without constructing a coherent backward orbit.")),
                    Paragraph(Text("Continuity is inherited from f by the subtype topology. The proof permits empty X and empty core, "
                        + "arbitrary compact Hausdorff topology, and nononto or noninvertible f. No positive-time, metric, countability "
                        + "or chosen-selector hypothesis occurs. This supplies a core system for later dynamics; it asserts no period or shadowing."))),
                DescribeRole.Theorem))));
}
