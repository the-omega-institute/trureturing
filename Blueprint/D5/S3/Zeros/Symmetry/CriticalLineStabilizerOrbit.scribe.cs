using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Symmetry;

internal sealed class CriticalLineStabilizerOrbitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var zeroData = F.Id("Z");
        var index = F.Id("n");
        var naturals = Seq(Mathbb, Grp(F.Id("N")));
        var zero = Seq(zeroData, Dot, F.Id("zero"), Open, index, Close);
        var reflection = Seq(zeroData, Dot, F.Id("reflection"), Open, index, Close);
        var conjugation = Seq(zeroData, Dot, F.Id("conjugation"), Open, index, Close);
        var mirror = Seq(
            zeroData, Dot, F.Id("conjugation"), Open,
            zeroData, Dot, F.Id("reflection"), Open, index, Close, Close);
        var localization = Grp(Seq(
            Forall, Sp, index, InMacro, Sp, naturals, Comma, Esc,
            Re, Open, zero, Close, Sp, Eq, Sp,
            Operatorname, Grp(F.Id("criticalAbscissa"))));
        var fixedIndices = Grp(Seq(
            Forall, Sp, index, InMacro, Sp, naturals, Comma, Esc,
            mirror, Sp, Eq, Sp, index));
        var fourPointOrbit = Grp(Seq(
            Exists, Sp, index, InMacro, Sp, naturals, Comma, Esc,
            Operatorname, Grp(F.Id("card")), OpenBrace,
            index, Comma, Sp, reflection, Comma, Sp, conjugation, Comma, Sp, mirror,
            CloseBrace, Sp, Eq, Sp, D(4)));
        var commute = Seq(
            Operatorname, Grp(F.Id("Commute")), Open,
            zeroData, Dot, F.Id("reflection"), Comma, Sp,
            zeroData, Dot, F.Id("conjugation"), Close);
        var statement = Disp(Seq(
            Forall, Sp, zeroData, Colon, Sp, Operatorname, Grp(F.Id("ZeroData")), Comma, Esc,
            Open, localization, Sp, Leftrightarrow, Sp, fixedIndices, Close,
            Sp, Land, Sp,
            Open, Neg, Sp, localization, Sp, Rightarrow, Sp, fourPointOrbit, Close,
            Sp, Land, Sp, commute));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Critical localization fixes every mirror index; outside it, a four-point orbit "
                + "appears without loss of the zero symmetries.",
            H("Critical-Line Stabilizers and Off-Line Orbits"),
            Blocks(Describe.Lean(
                DescribeId.Create("critical-localization-stabilizers-and-off-line-orbits"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/Symmetry/CriticalLineStabilizerOrbit."
                        + "critical_line_stabilizer_orbit_dichotomy"),
                H("Critical localization is stabilizer enlargement"),
                StatementSource.FromAuthor(statement),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For each supplied duplicate-free exhaustive ZeroData enumeration, "
                            + "all indexed zeros lie on the critical line exactly when "
                            + "conjugation after reflection fixes every index. If localization "
                            + "does not hold, one indexed zero has the full four-element "
                            + "reflection-conjugation orbit.")),
                    Paragraph(Text(
                        "The real-unit-interval nonvanishing theorem rules out a "
                            + "conjugation-fixed nontrivial zero, so the existing four-point "
                            + "orbit theorem applies to the off-line witness. Reflection and "
                            + "conjugation commute independently of localization, showing that "
                            + "the complete set symmetry remains present in both alternatives. "
                            + "The statement intentionally uses direct localization of supplied "
                            + "ZeroData rather than a global Riemann-hypothesis proposition."))),
                DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S3/Analytic/Zeta/RealUnitIntervalZetaNonvanishing")),
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S3/Zeros/Symmetry/ZeroOrbitCardinality")),
            ]));
    }
}
