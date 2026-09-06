using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.WeylChronology;

internal sealed class SchrodingerDisplacementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuous translations and phase multipliers realize the Weyl cocycle directly.",
        H("Continuous Weyl Displacements"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("continuous-weyl-cocycle"),
                DeclarationHandle.Create("D5/S3/Quantum/WeylChronology/SchrodingerDisplacement.displacement_comp"),
                H("Concrete composition law"),
                StatementSource.FromAuthor(Composition()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The carrier is real-coordinate complex wavefunctions. In dimensionless quadratures the action is exp(i(2yq-xy)) times f(q-x). The left operator acts last.")),
                    Paragraph(Text("The law is proved by complex exponential addition and translation arithmetic. No canonical-commutator axiom, finite Fock cutoff, or frozen finite-clock owner is substituted for a continuous action.")),
                    Paragraph(Text("This representation is classical. Vutha et al., arXiv:1702.01833, explain displacement composition. L2 completion, strong continuity and generator domains are outside this declaration."))),
                DescribeRole.Theorem))));

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Wavefunctions() =>
        Seq(Mathbb, Grp(F.Id("C")), Caret, Grp(Reals()));
    private static Formula Phase(Formula t) => Call("exp", Seq(F.Id("i"), Cdot, Grp(t)));

    private static Formula Composition()
    {
        Formula x=F.Id("x"), y=F.Id("y"), u=F.Id("u"), v=F.Id("v"), f=F.Id("f");
        return Disp(Seq(
            Forall, Sp, x, Comma, y, Comma, u, Comma, v, Colon, Reals(), Comma, Esc,
            Forall, Sp, f, Colon, Wavefunctions(), Comma, Esc,
            Call("displacement", x, y, Call("displacement", u, v, f)), Eq,
            Phase(Seq(y,Cdot,u,Minus,x,Cdot,v)), Cdot,
            Call("displacement", Grp(x,Plus,u), Grp(y,Plus,v), f)));
    }
}
