using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class StableCoreImageDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => F.Id(name);
    private static Formula All(string name, Formula type) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma);
    private static Formula Inst(string name, Formula type) =>
        Seq(OpenBracket, Call(name, type), CloseBracket);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, Rightarrow, Sp, b);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A value realizable at every finite predecessor depth has one realization in the stable core.",
        H("Stable Core Images and Coherent Predecessor Fibers"),
        Blocks(Describe.Lean(
            DescribeId.Create("continuous-observation-preserves-core-intersection"),
            DeclarationHandle.Create("D5/S1/Dynamics/Shadowing/StableCoreImage.image_stableCore_eq_iInter"),
            H("An observation commutes with the stable-core intersection"),
            StatementSource.FromAuthor(Disp(new Formula.Aligned([
                Seq(All("X", V("Type")), Sp, All("Y", V("Type"))),
                Seq(Grp(Inst("TopologicalSpace", V("X"))), Sp, Inst("CompactSpace", V("X")), Sp,
                    Inst("TTwoSpace", V("X"))),
                Seq(Grp(Inst("TopologicalSpace", V("Y"))), Sp, Inst("TOneSpace", V("Y"))),
                Seq(All("f", Arrow(V("X"), V("X"))), Sp,
                    All("q", Arrow(V("X"), V("Y")))),
                Seq(Call("Continuous", V("f")), Sp, Land, Sp,
                    Call("Continuous", V("q")), Sp, Rightarrow),
                Seq(Call("image", V("q"), Call("stableCore", V("f"))), Eq,
                    Call("Intersection", Call("observedIterateRanges", V("f"), V("q"))))
            ]))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let X:Type u be compact Hausdorff, Y:Type v have closed singletons, "
                    + "and f:X→X and q:X→Y be continuous. Universes are independent. With "
                    + "stableCore(f)=⋂n≥0 range(f^[n]), the exact set equality is "
                    + "q(stableCore(f))=⋂n≥0 q(range(f^[n])). Thus a value y which has some "
                    + "preimage in every forward image has a single preimage in their entire "
                    + "intersection. The witnesses at separate finite depths need not agree.")),
                Paragraph(Text(
                    "For the nonautomatic inclusion, fix y and intersect each compact iterate "
                    + "image with the closed fiber q⁻¹{y}. These sets are nonempty by the "
                    + "right-hand side hypothesis, and decrease because "
                    + "f^[n+1](X)⊆f^[n](X). Mathlib's compact nested-intersection theorem gives "
                    + "one point in every such fiber-image intersection. That point realizes y "
                    + "in the stable core. The other inclusion is ordinary image monotonicity. "
                    + "No exchange of arbitrary set images with intersections is assumed.")),
                Paragraph(Text(
                    "No finite alphabet, injectivity, surjectivity, recurrence, equicontinuity, "
                    + "source shadowing or Nonempty instance is required. Y need not be "
                    + "Hausdorff or compact. Empty X is included. A continuous whole-name map "
                    + "into a product of Hausdorff observation spaces fits the same telescope; "
                    + "the target need not be a finite collection of names.")),
                Paragraph(Text(
                    "Two consequences locate the next stable-core proof obligations. Taking "
                    + "q=f identifies f(stableCore(f)) with the intersection of the positive "
                    + "iterate images, which equals stableCore(f), since time zero adds X only. "
                    + "For a continuous onto q with q∘f=g∘q, the iterated semiconjugacy equation "
                    + "and surjectivity identify q(range(f^[n])) with range(g^[n]); hence "
                    + "q(stableCore(f))=stableCore(g). In particular every factor-core point "
                    + "has a source-core lift. These are applications of the intersection "
                    + "theorem, not separately retained wrapper declarations.")),
                Paragraph(Text(
                    "The repository's FactorImageStability.surjective_semiconj_iterate_ranges "
                    + "supplies individual iterate-image transport on a finite source, and "
                    + "StableCoreObservation supplies uniform exact observation tails from an "
                    + "assumed core period. Neither supplies this infinite common-fiber witness. "
                    + "The new compactness argument bridges finite predecessor depth to a "
                    + "whole stable core; it uses the existing compact intersection theorem "
                    + "rather than reproving it. It does not construct a zero-dimensional "
                    + "shadowing extension, prove equicontinuous finite observation periods, "
                    + "or establish the all-face array surjectivity of Peng Question 5.2. "
                    + "Unrestricted Questions 5.1 and 5.2 remain unresolved here, and no "
                    + "literature originality or worldwide-open claim is made. Utility kind "
                    + "is none: no checker, enumeration or numeric certificate is asserted."))),
            DescribeRole.Theorem))));
}
