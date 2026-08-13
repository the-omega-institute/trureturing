using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Phase.Interference;

internal sealed class M468MemberTableDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The m468 side column is computed by the frozen Jacobi selector; unsupported m-side and 1729 orbit claims are omitted.",
        H("M468 Member Table"),
        Blocks(
            Paragraph(Text(
                "The phase classifier and the frozen selector column are separate definitions. "
                + "The finite phase-member table records only prime labels and residue classes; it does not assume selector values.")),
            Describe.Lean(DescribeId.Create("m468-split-prime-characterization"),
                DeclarationHandle.Create(
                    "D5/S1/Phase/Interference/M468MemberTable.m468_split_prime_characterization"),
                H("Frozen selector side characterization"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("p"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Forall, Sp, F.Id("Psi"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")), Comma, Esc,
                    Open, F.Id("phaseMember"), Open, F.Id("p"), Comma, F.Id("Psi"), Close,
                    Rightarrow, Sp, Open,
                    F.Id("sameSide"), Open, F.Id("p"), Comma, F.Id("Psi"), Close, Sp, Leftrightarrow, Sp,
                    F.Id("Psi"), Sp, Operatorname, Grp(F.Id("mod")), Sp, D(2, 4), Eq, D(0),
                    Sp, Land, Sp,
                    F.Id("differentSide"), Open, F.Id("p"), Comma, F.Id("Psi"), Close, Sp, Leftrightarrow, Sp,
                    F.Id("Psi"), Sp, Operatorname, Grp(F.Id("mod")), Sp, D(2, 4), Eq, D(1, 2), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The side is defined from the split-factor Jacobi value J(-384 | p) in the frozen selector factorization. "
                    + "The checked selector column is J(-384 | 7) = 1 and J(-384 | 67) = -1; "
                    + "the independent phase-member table then connects those computed values to the two residue classes."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("m468-zero-only-failure"),
                DeclarationHandle.Create(
                    "D5/S1/Phase/Interference/M468MemberTable.m468_zero_only_fails"),
                H("Zero-only selector column fails at m468"),
                StatementSource.FromAuthor(Disp(Seq(
                    Esc, Neg, Sp, F.Id("zeroOnly"), Underscore, Grp(D(4, 6, 8))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Zero-only means that every proper prime divisor has frozen selector value zero. "
                    + "The equivalence to successor primality is proved separately; 469 = 7 * 67 and "
                    + "the prime divisor 7 with selector value J(-384 | 7) = 1 provides the non-vacuity witness."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "Disclosure: the frozen repository surface provides no m-side selector semantics and no "
                + "three-prime orbit bridge at 1729, so neither claim is asserted here.")))));
}
