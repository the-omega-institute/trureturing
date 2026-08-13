using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics;

internal sealed class DensePhaseEscapeIdentityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dense fixed-point scaling gives the decay identity only at finitely many realizable exponents.",
        H("Dense Phase Escape Identity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("dense-phase-realizable-exponents"),
                DeclarationHandle.Create(
                    "D5/S0/Asymptotics/DensePhaseEscapeIdentity.dense_phase_escape_identity_on_realizable_exponents"),
                H("Dense-phase identity on realizable exponents"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("Y"), Comma, Sp, F.Id("f"), Comma, Sp,
                    F.Id("A"), Comma, Sp, F.Id("n"), Comma, Sp, F.Id("k"), Comma, Sp, F.Id("c"),
                    Comma, Sp, Operatorname, Grp(F.Id("Finite")), Open, F.Id("Y"), Close,
                    Sp, Land, Sp, Operatorname, Grp(F.Id("Nonempty")), Open, F.Id("Y"), Close,
                    Sp, Land, Sp, D(2), Sp, Leq, Sp, F.Id("n"),
                    Sp, Land, Sp, Operatorname, Grp(F.Id("card")), Open, F.Id("Y"), Close,
                    Sp, Eq, Sp, F.Id("n"),
                    Sp, Land, Sp, D(0), Sp, Lt, Sp, F.Id("c"), Sp, Lt, Sp, D(1),
                    Sp, Land, Sp, Operatorname, Grp(F.Id("card")), Open,
                    Operatorname, Grp(F.Id("Fix")), Open, F.Id("f"), Close, Close,
                    Sp, Eq, Sp, F.Id("k"),
                    Sp, Land, Sp, F.Id("k"), Sp, Eq, Sp, F.Id("c"), Thin, F.Id("n"),
                    Caret, Grp(F.Id("A")), Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("escapeProbability")), Underscore,
                    Grp(Operatorname, Grp(F.Id("Fin")), Thin, F.Id("A")), Open, F.Id("f"), Close,
                    Sp, Eq, Sp, Open, D(1), Sp, Minus, Sp, F.Id("c"), Close,
                    Caret, Grp(F.Id("A")), Sp, Land, Sp,
                    Lim, Underscore, Grp(F.Id("B"), Sp, To, Sp, Infty),
                    Open, D(1), Sp, Minus, Sp, F.Id("c"), Close, Caret, Grp(F.Id("B")),
                    Sp, Eq, Sp, D(0), Sp, Land, Sp,
                    Exists, Sp, F.Id("A"), Underscore, D(0), Comma, Sp,
                    F.Id("A"), Sp, Lt, Sp, F.Id("A"), Underscore, D(0),
                    Sp, Land, Sp, Forall, Sp, F.Id("B"), Comma, Sp,
                    F.Id("A"), Underscore, D(0), Sp, Leq, Sp, F.Id("B"),
                    Sp, Rightarrow, Sp, Operatorname, Grp(F.Id("card")), Open,
                    Operatorname, Grp(F.Id("Fix")), Open, F.Id("f"), Close, Close,
                    Sp, Neq, Sp, F.Id("c"), Thin, F.Id("n"), Caret, Grp(F.Id("B")), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The exact escaped-listing cardinality reduces the repository's uniform "
                        + "escape probability to the stated power whenever the fixed-point count "
                        + "equals c times n to the address exponent.")),
                    Paragraph(Text(
                        "The power profile converges to zero because zero is less than c and c is "
                        + "less than one. This decay is an abstract profile, not an asymptotic family "
                        + "of realizable transformations.")),
                    Paragraph(Text(
                        "Indeed, the structural fixed-point bound supplies a finite cutoff A0. Every "
                        + "exponent satisfying the dense equation lies below A0, and the complete "
                        + "hypothesis bundle is witnessed concretely only at A = 1 in this module."))),
                DescribeRole.Theorem)),
        []));
}
