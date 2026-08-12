using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.HiddenFlow;

internal sealed class ContinuousRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuous additive real flows in the observer hidden-address space are trivial; "
            + "the canonical integer-cast jump is a separate nonzero witness.",
        H("Continuous Hidden-Flow Rigidity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("every-continuous-additive-real-hidden-flow-is-zero"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/HiddenFlow/ContinuousRigidity."
                        + "continuous_hidden_flow_eq_zero"),
                H("Every continuous additive real hidden flow is zero"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, Phi, Sp, InMacro, Sp,
                    Operatorname, Grp(F.Id("CAddHom")), Open,
                    Mathbb, Grp(F.Id("R")), Comma, Sp,
                    Prod, Underscore,
                    Grp(F.Id("p"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("P"))), Sp,
                    Mathbb, Grp(F.Id("Z")), Underscore, Grp(F.Id("p")), Close,
                    Comma, Sp, Phi, Sp, Eq, Sp, D(0), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The hidden address space is the product of the rings of p-adic integers "
                            + "over all primes. A continuous additive homomorphism from the real "
                            + "line into this product is constant because the source is connected "
                            + "and the target is totally disconnected. Additivity fixes the value "
                            + "at the identity parameter to zero, so the constant flow is exactly "
                            + "the zero homomorphism.")),
                    Paragraph(Text(
                        "This is a flow-level specialization of the repository's existing "
                            + "hidden-fiber rigidity theorem. It excludes a nontrivial continuous "
                            + "real parameterization of hidden address shifts. Its conclusion is "
                            + "only continuous real-flow exclusion: it does not classify all "
                            + "parameter groups, force a nontrivial action to be discrete or "
                            + "integer-valued, assert a crossed-product identification, or show "
                            + "that an observer premise selects this address space."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-canonical-integer-cast-hidden-jump-is-nonzero"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/HiddenFlow/ContinuousRigidity."
                        + "discreteHiddenJump_ne_zero"),
                H("The canonical integer-cast hidden jump is nonzero"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("discreteHiddenJump"), Sp, Neq, Sp, D(0), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The additive homomorphism sends an integer to its canonical cast in "
                            + "every p-adic coordinate. Evaluating at the integer one and the "
                            + "prime two gives one, which is nonzero. This is only an anti-vacuity "
                            + "witness for one chosen integer-parameter homomorphism. It is "
                            + "independent of the rigidity proof and does not show that every "
                            + "nontrivial hidden action is discrete, integer-valued, or selected "
                            + "by the observer premise."))),
                DescribeRole.Theorem))));
}
