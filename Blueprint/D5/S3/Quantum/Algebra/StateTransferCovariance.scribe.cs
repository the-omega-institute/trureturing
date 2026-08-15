using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class StateTransferCovarianceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pointwise reads intertwine finite-state pushforwards with pulled-back observables.",
        H("Finite-State Read Covariance"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pointwise-reads-intertwine-finite-state-pushforwards"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/StateTransferCovariance."
                    + "diagonal_state_transfer_covariance"),
                H("Pointwise reads intertwine finite-state pushforwards"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("Y"), Sp, Operatorname, Grp(F.Id("finite")), Comma, Sp,
                    Tau, Colon, Sp, F.Id("Y"), Sp, To, Sp, F.Id("Y"), Comma, Sp,
                    F.Id("f"), Colon, Sp, F.Id("Y"), Sp, To, Sp,
                    Mathbb, Grp(F.Id("C")), Comma, Esc,
                    Alpha, Underscore, Grp(Tau), Open, F.Id("f"), Close, Sp, Eq, Sp,
                    F.Id("f"), Sp, Circ, Sp, Tau, Comma, Quad, Sp,
                    F.Id("M"), Underscore, Grp(F.Id("f")), Sp, Circ, Sp,
                    F.Id("L"), Underscore, Grp(Tau), Sp, Eq, Sp,
                    F.Id("L"), Underscore, Grp(Tau), Sp, Circ, Sp,
                    F.Id("M"), Underscore,
                    Grp(Alpha, Underscore, Grp(Tau), Open, F.Id("f"), Close), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Y be a finite state type, let tau be any self-map of Y, and let f "
                            + "be a complex-valued observable. Write L_tau for the canonical "
                            + "finite pushforward and M_f for pointwise multiplication by f. "
                            + "Then M_f after L_tau equals L_tau after multiplication by the "
                            + "pulled-back observable f after tau.")),
                    Paragraph(Text(
                        "The Lean declaration uses the existing readObservable operator and "
                            + "mathlib's FunOnFinite.map without redefining either construction. "
                            + "It applies FunOnFinite.map_apply_apply to expose the fiber sum and "
                            + "Finset.mul_sum to distribute the read value; equality on each "
                            + "fiber identifies f(tau(y)) with f(z).")),
                    Paragraph(Text(
                        "Loogle and LeanSearch found the pushforward and its fiber-sum theorem, "
                            + "but no full covariance result. Repository and digestion-record "
                            + "searches likewise found no duplicate. The theorem allows arbitrary "
                            + "finite self-maps and does not assume reversibility."))),
                DescribeRole.Theorem))));
}
