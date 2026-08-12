using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Solenoid;

internal sealed class HiddenMotionRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Every continuous path in the prime-adic hidden fiber is constant.",
H("Hidden-Motion Rigidity"),
Blocks(
            Describe.Lean(
                DescribeId.Create("every-continuous-prime-adic-hidden-motion-is-constant"),
                DeclarationHandle.Create("D5/S1/Solenoid/HiddenMotionRigidity."
                    + "prime_adic_hidden_motion_rigidity"),
                H("Every continuous prime-adic hidden motion is constant"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("gamma"), Colon, Sp, F.Id("I"), Sp, To, Sp,
                    Prod, Underscore, Grp(F.Id("p"), InMacro, Sp, Mathbb, Grp(F.Id("P"))),
                    Sp, Mathbb, Grp(F.Id("Z")), Underscore, F.Id("p"), Comma, Sp,
                    Operatorname, Grp(F.Id("Continuous")), Open, F.Id("gamma"), Close,
                    Sp, Rightarrow, Sp, Forall, Sp, F.Id("s"), Comma, Sp, F.Id("t"),
                    Sp, InMacro, Sp, F.Id("I"), Comma, Sp,
                    F.Id("gamma"), Open, F.Id("s"), Close, Sp, Eq, Sp,
                    F.Id("gamma"), Open, F.Id("t"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The path domain is the closed unit interval, while the hidden codomain "
                    + "is the product of the rings of p-adic integers over all primes. Each "
                    + "p-adic factor is ultrametric and therefore totally disconnected; the "
                    + "product retains total disconnectedness. Mathlib's general rigidity "
                    + "theorem then makes any continuous map from the connected interval "
                    + "constant, excluding every genuine pure hidden continuous slide."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-total-disconnectedness-hypothesis-is-weight-bearing"),
                DeclarationHandle.Create("D5/S1/Solenoid/HiddenMotionRigidity."
                    + "real_unit_interval_has_nonconstant_continuous_motion"),
                H("The total-disconnectedness hypothesis is weight-bearing"),
                StatementSource.FromAuthor(Disp(Seq(
                    Exists, Sp, F.Id("gamma"), Colon, Sp, F.Id("I"), Sp, To, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, Sp,
                    Operatorname, Grp(F.Id("Continuous")), Open, F.Id("gamma"), Close,
                    Sp, Land, Sp, Exists, Sp, F.Id("s"), Comma, Sp, F.Id("t"), Comma, Sp,
                    F.Id("gamma"), Open, F.Id("s"), Close, Sp, Neq, Sp,
                    F.Id("gamma"), Open, F.Id("t"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Replacing the hidden codomain by the real line invalidates the rigidity "
                    + "conclusion: the subtype inclusion from the unit interval to the reals "
                    + "is continuous and sends zero and one to distinct values. This "
                    + "kernel-checked counterexample shows that total disconnectedness, not "
                    + "the path notation alone, carries the exclusion."))),
                DescribeRole.Theorem))));
}
