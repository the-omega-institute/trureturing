using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class FourExitRawEndpointSpectrumDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula And(params Formula[] xs) =>
        Seq(xs.Select((x, i) => i == 0 ? Par(x) : Seq(Sp, Land, Sp, Par(x))).ToArray());

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The four-exit right-comb family has explicit positive representatives and a raw endpoint menu interface.",
        H("Four-Exit Raw Endpoint Spectrum"),
        Blocks(
            Paragraph(Text(
                "This implementation fixes the literal blocks from Whitebox chapter 68 and reuses the "
                + "public Source, thirdImage, Positive, and actual-response cost interfaces. The right comb "
                + "has k active slots and one compensation slot; the indexed family has one baseline member "
                + "and four exceptional members per slot.")),
            Describe.Lean(
                DescribeId.Create("four-exit-family-base-properties"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/FibonacciAtomic/FourExitRawEndpointSpectrum.result"),
                H("Positive family, common size, and nonempty menu"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, V("k"), InMacro, Sp, Mathbb, Grp(V("N")), Comma, Sp,
                    D(1), Le, Sp, V("k"), Implies, Sp,
                    And(
                        Call("forallPositive", Call("family", V("k"))),
                    Call("forall", Call("familyLength", V("k"), Seq(D(8), Cdot, Sp, V("k"), Plus, D(1, 6)))),
                        Call("Nonempty", Call("menu", V("k"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The result supplies the concrete source preimages for every family member, "
                        + "proves positivity by the defining third iterate, computes each block length "
                        + "and the comb length symbolically, and exhibits a baseline endpoint in the menu.")),
                    Paragraph(Text(
                        "The full 68.12 Pareto statement is deliberately left open here: the local "
                        + "two-excess obstruction, the six tail controllers, and their actual cost vectors "
                        + "require additional response-history content beyond this compiled base interface.")),
                    Paragraph(Text(
                        "Consequently this document records only the verified base properties. Chapters "
                        + "68.13--68.15 and the common-seed or coarse-readout frontiers are outside this module."))),
                DescribeRole.Theorem))));
}
