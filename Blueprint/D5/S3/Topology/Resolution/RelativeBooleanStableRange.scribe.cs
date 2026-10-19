using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Resolution;

internal sealed class RelativeBooleanStableRangeDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/Resolution/RelativeBooleanStableRange.";
    private static Formula V(string n) => F.Id(n);
    private static Formula K => Call("core", V("f"));
    private static Formula G => Call("stableLift", V("f"), V("hf"));
    private static Formula Statement => Disp(new Formula.Aligned([
        Seq(Forall, Sp, V("X"), Colon, Sp, Call("Type", V("u")), Comma, Sp,
            OpenBracket, Call("TopologicalSpace", V("X")), CloseBracket),
        Seq(Forall, Sp, V("f"), Colon, Sp, V("X"), Sp, To, Sp, V("X"), Comma, Sp,
            Forall, Sp, V("hf"), Colon, Sp, Call("Continuous", V("f")), Comma),
        Seq(Call("Continuous", G), Sp, Land, Sp,
            Call("core", G), Sp, Eq, Sp,
            Call("preimage", Call("projection", K), K), Sp, Land),
        Call("Semiconj", Call("sectionC", K), Call("restriction", V("f")), G)
    ]));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual relative Boolean lift has exactly the inverse-image stable range and carries the continuous core section equivariantly.",
        H("Stable range of the relative Boolean lift"), Blocks(
            Describe.Lean(DescribeId.Create("actual-stable-lift-dynamics"),
                DeclarationHandle.Create(Owner + "stable_lift_dynamics"),
                H("Continuity, exact stable range and core action"), StatementSource.FromAuthor(Statement),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Topology/banaschewski1955nulldimensional")),
                Blocks(
                    Paragraph(Text("K is the actual intersection of range(f^n) over all natural n, including zero. Forward invariance supplies the pair-map hypothesis. "
                        + "stableLift(f,hf) is literally lift(f,hf,mapsTo_core(f)) on Space(K). It uses the same graph closure, membership coordinates "
                        + "and projection as the topology module. Continuity follows from the constructed ambient pair map and its restriction.")),
                    Paragraph(Text("For the forward inclusion in the stable-range equality, choose an upstairs n-step preimage and project it. "
                        + "The projection semiconjugacy, iterated with Mathlib's Semiconj.iterate_right, gives an n-step preimage downstairs. "
                        + "For the reverse inclusion, fix n and choose x with f^n(x)=projection(y). Take the actual graph point u=point(K,x). "
                        + "The n-step image of u projects to projection(y), which lies in K. The previously proved singleton fiber over that point "
                        + "therefore identifies this n-step image with y. This is a separate finite-n choice; no backward coherent orbit or ambient surjectivity is assumed.")),
                    Paragraph(Text("Semiconj(s,r,g) means s(r(c))=g(s(c)). Here s=sectionC(K), r=StableRange.restriction(f), and g=stableLift(f,hf). "
                        + "The graph-agreement law lift_point gives this equation for the actual continuous section. "
                        + "Its homeomorphism onto the full inverse image of K, together with the stable-range equality, identifies the actual lifted core with K.")),
                    Paragraph(Text("The displayed theorem needs only a topological X and continuous f. It includes empty X and K and all natural times. "
                        + "If X is additionally compact Hausdorff and K is zero-dimensional, is_closed_core proves K closed and "
                        + "functorial_resolution makes this same Space(K) compact Hausdorff with a clopen basis and continuous onto projection. "
                        + "compact_surjective_restriction supplies the compact onto source core system. No metric, countability, nonemptiness, "
                        + "positive-period, invertibility or global onto hypothesis is introduced.")),
                    Paragraph(Text("This exact construction is a supplier for later period and finite-observation arguments. Those hypotheses and shadowing conclusions "
                        + "are not part of this theorem. The classical Stone/Banaschewski attribution applies to the underlying compactification; "
                        + "the stable-range proof is a repository derivation. Unrestricted Peng Question 5.1 remains outside this result."))),
                DescribeRole.Theorem))));
}
