using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity;

internal sealed class MechanicalSubshiftMinimalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform recurrence makes every member of an irrational lower mechanical word subshift "
            + "share its factor language, hence every forward orbit is dense and no proper "
            + "nonempty closed shift-invariant subsystem exists.",
        H("Minimality of Irrational Lower Mechanical Word Subshifts"),
        Blocks(
            Paragraph(Text(
                "Fix an irrational slope alpha in the half-open interval from zero to one and "
                + "an arbitrary real intercept rho. Write X_alpha,rho for the prefix-language "
                + "subshift of the associated lower mechanical word and F_alpha,rho(n) for its "
                + "set of length-n factors.")),
            Describe.Lean(
                DescribeId.Create("mechanical-factor-reverse-inclusion"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/MechanicalSubshiftMinimality."
                        + "mechanical_wordFactorSet_subset_of_mem_wordSubshift"),
                H("Every base factor occurs in every subshift member"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("y"), InMacro, Sp, F.Id("X"), Underscore,
                    Grp(Alpha, Comma, Sp, Rho), Sp, Rightarrow, Sp,
                    F.Id("F"), Underscore, Grp(Alpha, Comma, Sp, Rho), Open,
                    F.Id("n"), Close, Sp, Subseteq, Sp, F.Id("F"), Underscore,
                    Grp(F.Id("y")), Open, F.Id("n"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Choose a uniform recurrence bound for the prescribed mechanical factor, "
                    + "then realize a base-word window of that length as the prefix of y. The "
                    + "factor returns wholly inside this window, and translating its start gives "
                    + "an occurrence in y."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mechanical-member-language-equality"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/MechanicalSubshiftMinimality."
                        + "mechanical_wordFactorSet_eq_of_mem_wordSubshift"),
                H("Every subshift member has the base mechanical language"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("y"), InMacro, Sp, F.Id("X"), Underscore,
                    Grp(Alpha, Comma, Sp, Rho), Sp, Rightarrow, Sp,
                    F.Id("F"), Underscore, Grp(F.Id("y")), Open, F.Id("n"),
                    Close, Sp, Eq, Sp, F.Id("F"), Underscore,
                    Grp(Alpha, Comma, Sp, Rho), Open, F.Id("n"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The general subshift inclusion rules out new factors in y, while uniform "
                    + "recurrence supplies the reverse inclusion. The two inclusions give "
                    + "equality at every finite length."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mechanical-member-generates-same-subshift"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/MechanicalSubshiftMinimality."
                        + "wordSubshift_eq_of_mem_mechanical_wordSubshift"),
                H("Every member generates the same mechanical subshift"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("y"), InMacro, Sp, F.Id("X"), Underscore,
                    Grp(Alpha, Comma, Sp, Rho), Sp, Rightarrow, Sp,
                    F.Id("X"), Underscore, Grp(F.Id("y")), Sp, Eq, Sp,
                    F.Id("X"), Underscore, Grp(Alpha, Comma, Sp, Rho)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A prefix-language subshift is determined length by length by its factor "
                    + "sets, so equality of all finite languages gives equality of the generated "
                    + "subshifts."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mechanical-subshift-minimal"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/MechanicalSubshiftMinimality."
                        + "mechanical_wordSubshift_minimal"),
                H("Every forward orbit is dense in the mechanical subshift"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("y"), InMacro, Sp, F.Id("X"), Underscore,
                    Grp(Alpha, Comma, Sp, Rho), Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("cl")), Open, Operatorname,
                    Grp(F.Id("Orb")), Caret, Grp(Plus), Open, F.Id("y"), Close,
                    Close, Sp, Eq, Sp, F.Id("X"), Underscore,
                    Grp(Alpha, Comma, Sp, Rho)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The closure of a word's forward shift orbit is its prefix-language subshift. "
                    + "Since every member generates X_alpha,rho, its orbit closure is exactly "
                    + "X_alpha,rho."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("no-proper-mechanical-subsystem"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/MechanicalSubshiftMinimality."
                        + "mechanical_wordSubshift_eq_of_isClosed_shift_invariant"),
                H("There is no proper nonempty closed invariant subsystem"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("S"), Sp, Subseteq, Sp, F.Id("X"), Underscore,
                    Grp(Alpha, Comma, Sp, Rho), Sp, Land, Sp, F.Id("S"), Sp,
                    Neq, Sp, Emptyset, Sp, Land, Sp, Operatorname,
                    Grp(F.Id("Closed")), Open, F.Id("S"), Close, Sp, Land, Sp,
                    SigmaLower, Open, F.Id("S"), Close, Sp, Subseteq, Sp,
                    F.Id("S"), Sp, Rightarrow, Sp, F.Id("S"), Sp, Eq, Sp,
                    F.Id("X"), Underscore, Grp(Alpha, Comma, Sp, Rho)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Choose a member y of the subsystem. Shift invariance contains its whole "
                    + "forward orbit, closedness contains the orbit closure, and minimality makes "
                    + "that closure all of X_alpha,rho. The assumed reverse inclusion then gives "
                    + "equality. No intercept-independence statement or AddAction.IsMinimal "
                    + "registration is asserted here."))),
                DescribeRole.Theorem))));
}
