using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation;

internal sealed class LeCamDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Le Cam's finite two-point lemma bounds every test's total and maximum error masses by the total variation between its candidate laws.",
        H("Le Cam's Two-Point Lemma for Every Finite Test"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("le-cam-forces-one-error-mass-of-every-test-to-be-large"),
                DeclarationHandle.Create("D5/S3/Estimation/LeCam.le_cam_two_point_max"),
                H("Le Cam forces one error mass of every test to be large"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Begin, Grp(F.Id("gathered")),
                                    Forall, Sp, Iota, Esc,
                                    OpenBracket,
                                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                                    CloseBracket, Comma, RowBreak,
                                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                                    Forall, Sp, F.Id("A"), Colon, Sp,
                                    Operatorname, Grp(F.Id("Finset")), Open, Iota, Close, Comma, RowBreak,
                                    Open,
                                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                                    F.Id("p"), Open, F.Id("i"), Close, Eq,
                                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                                    F.Id("q"), Open, F.Id("i"), Close,
                                    Close, Sp, Land, Sp,
                                    Open,
                                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                                    F.Id("q"), Open, F.Id("i"), Close, Eq, D(1),
                                    Close, Sp, Rightarrow, Sp, RowBreak,
                                    Frac,
                                    Grp(
                                        D(1), Minus,
                                        Operatorname, Grp(F.Id("TV")),
                                        Open, F.Id("p"), Comma, Sp, F.Id("q"), Close),
                                    Grp(D(2)),
                                    Le, Sp, Max, Sp, Left, OpenBrace,
                                    Sum, Sp, Underscore,
                                    Grp(F.Id("i"), InMacro, Sp, F.Id("A")), Sp,
                                    F.Id("p"), Open, F.Id("i"), Close, Comma, Sp,
                                    Sum, Sp, Underscore,
                                    Grp(
                                        F.Id("i"), InMacro, Sp,
                                        F.Id("A"), Caret, F.Id("c")), Sp,
                                    F.Id("q"), Open, F.Id("i"), Close,
                                    Right, CloseBrace, Dot,
                                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "Le Cam's two-point lemma is the second major family of " +
                                        "information-theoretic lower bounds in this bucket, beside Fano's " +
                                        "inequality. Fano converts conditional entropy into an estimator-error " +
                                        "bound; Le Cam instead converts the statistical distance between two " +
                                        "candidate laws into a test-error bound. For unit-mass laws, no test can " +
                                        "drive its total error below one minus their total variation. The " +
                                        "mechanisms differ, but both prevent uniformly reliable inference.")),
                                    Paragraph(Text(
                                        "The acceptance region A is universally quantified, and this is the " +
                                        "content of the statement. The test reports q on A, so its two error " +
                                        "masses are the p-mass of A and the q-mass of the complement of A. The " +
                                        "bound holds for every such A, hence for every test, rather than for a " +
                                        "conveniently selected event. A result restricted to one particular " +
                                        "acceptance region would provide no lower bound on arbitrary tests.")),
                                    Paragraph(Text(
                                        "The three declarations form a deliberate hierarchy. The base theorem " +
                                        "le_cam_two_point_sum_mass assumes only that p and q have equal total " +
                                        "mass and lower-bounds the sum of the two error masses by that common " +
                                        "mass minus total variation. It assumes no coordinatewise nonnegativity: " +
                                        "the frozen variational lever already applies to arbitrary real functions " +
                                        "of equal mass, and the remaining argument is purely order-theoretic and " +
                                        "algebraic. The theorem le_cam_two_point_sum adds unit mass only to rewrite " +
                                        "the common total as one. Finally, le_cam_two_point_max passes from the " +
                                        "sum to the displayed maximum bound.")),
                                    Paragraph(Text(
                                        "The proof is short because the required structural work has already been " +
                                        "frozen in total_variation_eq_sup_event_gap. It applies that variational " +
                                        "characterization to the supplied event A, takes only the upper-bound half " +
                                        "of its IsGreatest conclusion--no event gap exceeds total variation--and " +
                                        "adds the complement identity for q. It does not use the attainment half: " +
                                        "Le Cam bounds an already supplied test and does not select an optimizing " +
                                        "event. The module therefore consumes the characterization rather than " +
                                        "re-deriving it, which is precisely why that characterization was worth " +
                                        "proving.")),
                                    Paragraph(Text(
                                        "The maximum form is the operational conclusion. A maximum is at least the " +
                                        "average of its two entries, so every test has at least one error mass no " +
                                        "smaller than one half of one minus total variation. Equivalently, no test " +
                                        "can make both error masses smaller than that threshold simultaneously.")),
                                    Paragraph(Text(
                                        "The lower bound is tight. For two identical unit laws, total variation is " +
                                        "zero, while the acceptance region and its complement partition the total " +
                                        "mass. The two error masses therefore sum to one for every test, making the " +
                                        "sum bound an equality for every acceptance region. A test cannot " +
                                        "distinguish identical laws, and the lemma states exactly that obstruction.")),
                                    Paragraph(Text(
                                        "The inequality is not an identity. On Bool, take the two opposite unit " +
                                        "point masses and the empty acceptance region. Their total variation is " +
                                        "one, so the lower bound is zero, whereas the test's total error mass is " +
                                        "one; the inequality is strict. The checks that neither rfl nor simp closes " +
                                        "any of the three general bounds were compiled as fail_if_success " +
                                        "obligations.")),
                                    Paragraph(Text(
                                        "No minimax or sample-complexity corollary, multi-point generalization of " +
                                        "Assouad or Fano type, converse, or measure-theoretic analogue is claimed. " +
                                        "Divergences elsewhere in this program are measured in nats, although the " +
                                        "present lemma contains no logarithm and hence introduces no logarithmic " +
                                        "unit."))),
                DescribeRole.Theorem
            ))));
}
