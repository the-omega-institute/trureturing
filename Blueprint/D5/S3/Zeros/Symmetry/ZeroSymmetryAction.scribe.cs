using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Symmetry;

internal sealed class ZeroSymmetryActionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A supplied zero enumeration transports reflection and conjugation to commuting index actions.",
        H("Zero Symmetry Action"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zero-reflection-and-conjugation-commute"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/Symmetry/ZeroSymmetryAction.zero_symmetries_commute"),
                H("Zero reflection and conjugation commute"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("Z"), Colon, Sp,
                    Operatorname, Grp(F.Id("ZeroData")), Comma, Esc,
                    Operatorname, Grp(F.Id("Commute")), Open,
                    F.Id("Z"), Dot, F.Id("reflection"), Comma, Sp,
                    F.Id("Z"), Dot, F.Id("conjugation"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every supplied ZeroData value, the reflection and conjugation "
                    + "permutations commute. The proof compares their enumerated zeros and uses "
                    + "duplicate-freeness; it constructs no zero enumeration and assumes no "
                    + "critical-line statement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mirror-index-fixed-exactly-on-the-critical-line"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/Symmetry/ZeroSymmetryAction."
                    + "mirror_index_fixed_iff_critical"),
                H("A mirror index is fixed exactly on the critical line"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("Z"), Colon, Sp,
                    Operatorname, Grp(F.Id("ZeroData")), Comma, Esc,
                    Forall, Sp, F.Id("n"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    F.Id("Z"), Dot, F.Id("conjugation"), Open,
                    F.Id("Z"), Dot, F.Id("reflection"), Open, F.Id("n"), Close, Close,
                    Sp, Leftrightarrow, Sp,
                    Re, Open, F.Id("Z"), Dot, F.Id("zero"), Open, F.Id("n"), Close, Close,
                    Sp, Eq, Sp, Operatorname, Grp(F.Id("criticalAbscissa")), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each index of a supplied ZeroData value, conjugation after reflection "
                    + "fixes the index exactly when the indexed zero has critical real part. "
                    + "The forward direction lifts index equality to mirror fixedness and applies "
                    + "the repository's fixed-point theorem; the reverse direction uses "
                    + "enumeration injectivity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("all-nontrivial-zeros-critical-exactly-when-mirror-indices-fixed"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/Symmetry/ZeroSymmetryAction."
                    + "all_nontrivial_zeros_critical_iff_mirror_indices_fixed"),
                H("All nontrivial zeros are critical exactly when mirror indices are fixed"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("Z"), Colon, Sp,
                    Operatorname, Grp(F.Id("ZeroData")), Comma, Esc,
                    Open, Forall, Sp, Rho, InMacro, Sp, Mathbb, Grp(F.Id("C")), Comma, Esc,
                    Operatorname, Grp(F.Id("IsNontrivialZero")), Open, Rho, Close,
                    Sp, Rightarrow, Sp, Re, Open, Rho, Close, Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("criticalAbscissa")), Close,
                    Sp, Leftrightarrow, Sp,
                    Forall, Sp, F.Id("n"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    F.Id("Z"), Dot, F.Id("conjugation"), Open,
                    F.Id("Z"), Dot, F.Id("reflection"), Open, F.Id("n"), Close, Close,
                    Sp, Eq, Sp, F.Id("n"), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Conditional on a supplied duplicate-free exhaustive ZeroData enumeration, "
                    + "every classical nontrivial zero lies on the critical line exactly when "
                    + "every conjugate-reflection index is fixed. Exhaustiveness transports the "
                    + "indexwise equivalence to arbitrary nontrivial zeros. The theorem constructs "
                    + "no ZeroData inhabitant and therefore makes no unconditional Riemann "
                    + "hypothesis claim."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Weil/ReflectionLedger")),
        ]));
}
