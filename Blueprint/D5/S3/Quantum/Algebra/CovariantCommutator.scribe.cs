using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class CovariantCommutatorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Covariance factors commutators independently of any particular representation.",
        H("Covariant Commutator Factorization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("semiconjugacy-factors-the-commutator"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/CovariantCommutator.covariant_commutator_formula"),
                H("Semiconjugacy factors the commutator"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("U"), Comma, F.Id("f"), Comma, F.Id("t"), Sp,
                    InMacro, Sp, F.Id("B"), Comma, Esc, Sp,
                    F.Id("U"), Sp, F.Id("f"), Sp, Eq, Sp, F.Id("t"), Sp, F.Id("U"), Sp,
                    Rightarrow, Sp,
                    F.Id("U"), Sp, F.Id("f"), Sp, Minus, Sp,
                    F.Id("f"), Sp, F.Id("U"), Sp, Eq, Sp,
                    Open, F.Id("t"), Sp, Minus, Sp, F.Id("f"), Close, Sp, F.Id("U"), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For elements U, f, and t in any associative ring, the covariance "
                            + "equation U f = t U rewrites the oriented commutator as "
                            + "U f - f U = (t - f) U. In Lean, SemiconjBy carries exactly "
                            + "this covariance equation, and sub_mul supplies the entire "
                            + "factorization after rewriting.")),
                    Paragraph(Text(
                        "No topology, norm, star operation, completion, concrete representation, "
                            + "or universal property enters this declaration. It is only the "
                            + "representation-independent algebraic consequence of covariance."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-opposite-commutator-has-the-opposite-difference"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/CovariantCommutator.covariant_opposite_commutator_formula"),
                H("The opposite commutator has the opposite difference"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("U"), Comma, F.Id("f"), Comma, F.Id("t"), Sp,
                    InMacro, Sp, F.Id("B"), Comma, Esc, Sp,
                    F.Id("U"), Sp, F.Id("f"), Sp, Eq, Sp, F.Id("t"), Sp, F.Id("U"), Sp,
                    Rightarrow, Sp,
                    F.Id("f"), Sp, F.Id("U"), Sp, Minus, Sp,
                    F.Id("U"), Sp, F.Id("f"), Sp, Eq, Sp,
                    Open, F.Id("f"), Sp, Minus, Sp, F.Id("t"), Close, Sp, F.Id("U"), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Reversing the commutator orientation reverses the translated "
                            + "difference while leaving the common right factor U unchanged. "
                            + "This corollary records the sign convention explicitly instead "
                            + "of requiring downstream users to negate the first formula."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("every-covariant-group-pair-obeys-the-factorization"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/CovariantCommutator.covariant_pair_commutator_formula"),
                H("Every covariant group pair obeys the factorization"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("g"), Sp, InMacro, Sp, F.Id("Gamma"), Comma,
                    F.Id("a"), Sp, InMacro, Sp, F.Id("A"), Comma, Esc, Sp,
                    F.Id("U"), Underscore, Grp(F.Id("g")), Sp,
                    Operatorname, Grp(F.Id("embed")), Open, F.Id("a"), Close, Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("embed")), Open,
                    F.Id("action"), Underscore, Grp(F.Id("g")), Open, F.Id("a"), Close,
                    Close, Sp, F.Id("U"), Underscore, Grp(F.Id("g")), Sp,
                    Rightarrow, Sp,
                    F.Id("U"), Underscore, Grp(F.Id("g")), Sp,
                    Operatorname, Grp(F.Id("embed")), Open, F.Id("a"), Close, Sp,
                    Minus, Sp,
                    Operatorname, Grp(F.Id("embed")), Open, F.Id("a"), Close, Sp,
                    F.Id("U"), Underscore, Grp(F.Id("g")), Sp, Eq, Sp,
                    Open,
                    Operatorname, Grp(F.Id("embed")), Open,
                    F.Id("action"), Underscore, Grp(F.Id("g")), Open, F.Id("a"), Close,
                    Close, Sp, Minus, Sp,
                    Operatorname, Grp(F.Id("embed")), Open, F.Id("a"), Close,
                    Close, Sp, F.Id("U"), Underscore, Grp(F.Id("g")), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let a group act on a source semiring by ring equivalences, let embed "
                            + "map the source into an arbitrary target ring, and let U assign "
                            + "a target-ring unit to every group element. Pointwise covariance "
                            + "is a SemiconjBy hypothesis, so the generic factorization applies "
                            + "to every group element and source observable.")),
                    Paragraph(Text(
                        "The companion declaration covariant_pair_opposite_commutator_formula "
                            + "records the reversed orientation for the same covariant pair. "
                            + "These declarations do not construct a crossed product or assert "
                            + "that a given observer interface uniquely forces one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-two-address-window-is-a-noncommuting-covariant-pair"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/CovariantCommutator.window_two_covariant_commutator_witness"),
                H("The two-address window is a noncommuting covariant pair"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("C"), Sp, Eq, Sp, Operatorname, Grp(F.Id("clock")), Open, D(2), Close,
                    Comma, Sp,
                    F.Id("S"), Sp, Eq, Sp, Operatorname, Grp(F.Id("shift")), Open, D(2), Close,
                    Comma, Sp,
                    F.Id("r"), Sp, Eq, Sp, Operatorname, Grp(F.Id("root")), Open, D(2), Close,
                    Comma, Esc, Sp,
                    F.Id("C"), Sp, F.Id("S"), Sp, Eq, Sp,
                    Open, F.Id("r"), Sp, F.Id("S"), Close, Sp, F.Id("C"), Sp,
                    Land, Sp,
                    F.Id("C"), Sp, F.Id("S"), Sp, Minus, Sp,
                    F.Id("S"), Sp, F.Id("C"), Sp, Neq, Sp, D(0), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For the existing two-address finite window, the clock semiconjugates "
                            + "the cyclic shift to the primitive phase times that shift. This "
                            + "is the finite Weyl relation rewritten with the scalar on the "
                            + "shift before multiplication by the clock.")),
                    Paragraph(Text(
                        "The commutator is explicitly nonzero. If it vanished, the Weyl relation "
                            + "would force the primitive phase to fix the shift-clock product. "
                            + "At matrix entry (0,1), that product equals the primitive phase "
                            + "itself; cancellation would make the order-two primitive root equal "
                            + "to one, contradicting primitivity. Thus both the covariance premise "
                            + "and a genuinely noncommuting instance are inhabited."))),
                DescribeRole.Theorem))));
}
