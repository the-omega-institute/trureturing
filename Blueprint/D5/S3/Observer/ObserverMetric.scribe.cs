using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer;

internal sealed class ObserverMetricDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Permutation update defects characterize commutation, cyclic invariants, and a finite perturbation seminorm.",
        H("Observer Update Defects and Their Perturbation Seminorm"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("read-update-commutation-is-equivalent-to-zero-defect"),
                DeclarationHandle.Create("D5/S3/Observer/ObserverMetric.commute_iff_updateDefect_eq_zero"),
                H("Read-update commutation is equivalent to zero defect"),
                StatementSource.FromAuthor(CommuteFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "Let a register on I be a complex-valued amplitude function. The read "
                                        + "R_f multiplies amplitudes pointwise by f, while the permutation update "
                                        + "U_tau acts by pullback. The update defect is "
                                        + "delta_tau f(i) = f(tau^{-1} i) - f(i). The established read-update "
                                        + "commutator formula identifies this defect as the coefficient of the "
                                        + "represented commutator. If every register commutes, applying the "
                                        + "identity to the constant-one register extracts each coefficient. "
                                        + "Conversely, zero defect makes every coefficient times every predecessor "
                                        + "amplitude vanish. This finite-register theorem asserts no universal "
                                        + "C*-algebra, operator norm, Connes metric, or Rieffel structure."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("zero-defect-is-equivalent-to-update-invariance"),
                DeclarationHandle.Create("D5/S3/Observer/ObserverMetric.updateDefect_eq_zero_iff_invariant"),
                H("Zero defect is equivalent to update invariance"),
                StatementSource.FromAuthor(InvarianceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                                    "The defect uses the inverse permutation because updates act by pullback, "
                                    + "whereas invariance is stated in the forward coordinate. Evaluating a zero "
                                    + "defect at tau(i) gives f(i) = f(tau(i)); in the reverse direction, applying "
                                    + "forward invariance at tau^{-1}(i) cancels every defect coordinate. Thus the "
                                    + "kernel is characterized without a finiteness or inhabitance assumption."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("cyclic-window-invariants-are-exactly-constant"),
                DeclarationHandle.Create("D5/S3/Observer/ObserverMetric.invariant_iff_const_on_cyclic_window"),
                H("Cyclic-window invariants are exactly constant"),
                StatementSource.FromAuthor(CyclicWindowFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                                    "On the nonempty cyclic window ZMod M, the update is addition by one. Zero "
                                    + "defect first becomes invariance under this successor. Every residue has a "
                                    + "natural-number representative, so induction along successive additions "
                                    + "shows that its value equals f(0). Constant functions are invariant "
                                    + "immediately. This is the precise finite-window form of the statement that "
                                    + "the common observables are constants."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("the-perturbation-seminorm-vanishes-exactly-on-invariants"),
                DeclarationHandle.Create("D5/S3/Observer/ObserverMetric.perturbationSeminorm_eq_zero_iff"),
                H("The perturbation seminorm vanishes exactly on invariants"),
                StatementSource.FromAuthor(SeminormKernelFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                                    "For a finite nonempty index type, define L_tau(f) as the maximum of "
                                    + "|delta_tau f(i)| over all indices. If this maximum is zero, every "
                                    + "nonnegative coordinate norm is bounded above by zero and hence every "
                                    + "defect coordinate vanishes. The converse is immediate from the same finite "
                                    + "maximum. Combining this fact with the forward-invariance characterization "
                                    + "identifies the seminorm kernel exactly."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("the-perturbation-seminorm-is-subadditive"),
                DeclarationHandle.Create("D5/S3/Observer/ObserverMetric.perturbationSeminorm_add_le"),
                H("The perturbation seminorm is subadditive"),
                StatementSource.FromAuthor(SeminormAddFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                                    "The update defect is additive in the observable. At each index, the complex "
                                    + "triangle inequality bounds the defect of f + g by the sum of the two "
                                    + "defect norms. Each summand is then bounded by its own finite maximum, "
                                    + "yielding subadditivity of L_tau."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("the-perturbation-seminorm-is-absolutely-homogeneous"),
                DeclarationHandle.Create("D5/S3/Observer/ObserverMetric.perturbationSeminorm_smul"),
                H("The perturbation seminorm is absolutely homogeneous"),
                StatementSource.FromAuthor(SeminormSmulFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                                    "Scalar multiplication factors c out of every defect coordinate, and the "
                                    + "complex norm converts that factor to |c|. Since |c| is nonnegative, it "
                                    + "also factors through the finite maximum. Together with subadditivity and "
                                    + "the kernel theorem, this establishes the claimed perturbation seminorm "
                                    + "laws on finite nonempty windows."))),
                DescribeRole.Theorem
            ))));

    private static Formula CommuteFormula() => Disp(Seq(
        Begin, Grp(F.Id("gathered")), Sp,
        Forall, Sp, F.Id("I"), Comma, Esc,
        Forall, Sp, Tau, Sp, InMacro, Sp,
        Operatorname, Grp(F.Id("Perm")), Open, F.Id("I"), Close, Comma, Esc,
        Forall, Sp, F.Id("f"), Colon, Sp,
        F.Id("I"), To, Sp, Mathbb, Grp(F.Id("C")), Comma, RowBreak, Sp,
        Open, Forall, Sp, Psi, Colon, Sp,
        F.Id("I"), To, Sp, Mathbb, Grp(F.Id("C")), Comma, Esc,
        F.Id("U"), Underscore, Grp(Tau), Open,
        F.Id("R"), Underscore, Grp(F.Id("f")), Psi, Close,
        Eq, F.Id("R"), Underscore, Grp(F.Id("f")), Open,
        F.Id("U"), Underscore, Grp(Tau), Psi, Close, Close,
        Sp, Leftrightarrow, Sp,
        DeltaLower, Underscore, Grp(Tau), F.Id("f"), Eq, D(0), Dot,
        Sp, End, Grp(F.Id("gathered"))));

    private static Formula InvarianceFormula() => Disp(Seq(
        Forall, Sp, F.Id("I"), Comma, Esc,
        Forall, Sp, Tau, Sp, InMacro, Sp,
        Operatorname, Grp(F.Id("Perm")), Open, F.Id("I"), Close, Comma, Esc,
        Forall, Sp, F.Id("f"), Colon, Sp,
        F.Id("I"), To, Sp, Mathbb, Grp(F.Id("C")), Comma, Esc,
        DeltaLower, Underscore, Grp(Tau), F.Id("f"), Eq, D(0),
        Sp, Leftrightarrow, Sp,
        Forall, Sp, F.Id("i"), InMacro, Sp, F.Id("I"), Comma, Esc,
        F.Id("f"), Open, Tau, Sp, F.Id("i"), Close,
        Eq, F.Id("f"), Open, F.Id("i"), Close, Dot));

    private static Formula CyclicWindowFormula() => Disp(Seq(
        Begin, Grp(F.Id("gathered")), Sp,
        Forall, Sp, F.Id("M"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
        F.Id("M"), Neq, Sp, D(0), Sp, Rightarrow, Sp,
        Forall, Sp, F.Id("f"), Colon, Sp,
        Operatorname, Grp(F.Id("ZMod")), Open, F.Id("M"), Close,
        To, Sp, Mathbb, Grp(F.Id("C")), Comma, RowBreak, Sp,
        DeltaLower, Underscore, Grp(Plus, D(1)), F.Id("f"), Eq, D(0),
        Sp, Leftrightarrow, Sp,
        Exists, Sp, F.Id("c"), InMacro, Sp, Mathbb, Grp(F.Id("C")), Comma, Esc,
        F.Id("f"), Eq, Open, F.Id("i"), Mapsto, Sp, F.Id("c"), Close, Dot,
        Sp, End, Grp(F.Id("gathered"))));

    private static Formula SeminormKernelFormula() => Disp(Seq(
        Begin, Grp(F.Id("gathered")), Sp,
        Forall, Sp, F.Id("I"), Comma, Esc,
        D(0), Lt, Vert, Sp, F.Id("I"), Vert, Lt, Infty, Comma, Esc,
        Forall, Sp, Tau, Sp, InMacro, Sp,
        Operatorname, Grp(F.Id("Perm")), Open, F.Id("I"), Close, Comma, Esc,
        Forall, Sp, F.Id("f"), Colon, Sp,
        F.Id("I"), To, Sp, Mathbb, Grp(F.Id("C")), Comma, RowBreak, Sp,
        F.Id("L"), Underscore, Grp(Tau), Open, F.Id("f"), Close, Eq, D(0),
        Sp, Leftrightarrow, Sp,
        Forall, Sp, F.Id("i"), InMacro, Sp, F.Id("I"), Comma, Esc,
        F.Id("f"), Open, Tau, Sp, F.Id("i"), Close,
        Eq, F.Id("f"), Open, F.Id("i"), Close, Dot,
        Sp, End, Grp(F.Id("gathered"))));

    private static Formula SeminormAddFormula() => Disp(Seq(
        Begin, Grp(F.Id("gathered")), Sp,
        Forall, Sp, F.Id("I"), Comma, Esc,
        D(0), Lt, Vert, Sp, F.Id("I"), Vert, Lt, Infty, Comma, Esc,
        Forall, Sp, Tau, Sp, InMacro, Sp,
        Operatorname, Grp(F.Id("Perm")), Open, F.Id("I"), Close, Comma, RowBreak, Sp,
        Forall, Sp, F.Id("f"), Comma, F.Id("g"), Colon, Sp,
        F.Id("I"), To, Sp, Mathbb, Grp(F.Id("C")), Comma, Esc,
        F.Id("L"), Underscore, Grp(Tau), Open,
        F.Id("f"), Plus, F.Id("g"), Close,
        Leq, Sp, F.Id("L"), Underscore, Grp(Tau), Open, F.Id("f"), Close,
        Plus, F.Id("L"), Underscore, Grp(Tau), Open, F.Id("g"), Close, Dot,
        Sp, End, Grp(F.Id("gathered"))));

    private static Formula SeminormSmulFormula() => Disp(Seq(
        Begin, Grp(F.Id("gathered")), Sp,
        Forall, Sp, F.Id("I"), Comma, Esc,
        D(0), Lt, Vert, Sp, F.Id("I"), Vert, Lt, Infty, Comma, Esc,
        Forall, Sp, Tau, Sp, InMacro, Sp,
        Operatorname, Grp(F.Id("Perm")), Open, F.Id("I"), Close, Comma, RowBreak, Sp,
        Forall, Sp, F.Id("c"), InMacro, Sp, Mathbb, Grp(F.Id("C")), Comma, Esc,
        Forall, Sp, F.Id("f"), Colon, Sp,
        F.Id("I"), To, Sp, Mathbb, Grp(F.Id("C")), Comma, Esc,
        F.Id("L"), Underscore, Grp(Tau), Open,
        F.Id("c"), F.Id("f"), Close,
        Eq, Vert, Sp, F.Id("c"), Vert, Sp,
        F.Id("L"), Underscore, Grp(Tau), Open, F.Id("f"), Close, Dot,
        Sp, End, Grp(F.Id("gathered"))));
}
