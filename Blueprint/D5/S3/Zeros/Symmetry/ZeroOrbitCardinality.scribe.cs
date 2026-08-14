using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Symmetry;

internal sealed class ZeroOrbitCardinalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Off the critical line, a supplied nonreal zero index has a four-point symmetry orbit.",
        H("Zero Orbit Cardinality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("off-line-zero-indices-have-four-point-orbits"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/Symmetry/ZeroOrbitCardinality."
                    + "zero_orbit_card_four_of_off_line"),
                H("An off-line zero index has a four-point orbit"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("Z"), Colon, Sp,
                    Operatorname, Grp(F.Id("ZeroData")), Comma, Esc,
                    Forall, Sp, F.Id("n"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    F.Id("Z"), Dot, F.Id("conjugation"), Open, F.Id("n"), Close,
                    Sp, Neq, Sp, F.Id("n"), Sp, Land, Sp,
                    Re, Open, F.Id("Z"), Dot, F.Id("zero"), Open, F.Id("n"), Close, Close,
                    Sp, Neq, Sp, Operatorname, Grp(F.Id("criticalAbscissa")),
                    Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("card")), OpenBrace,
                    F.Id("n"), Comma, Sp,
                    F.Id("Z"), Dot, F.Id("reflection"), Open, F.Id("n"), Close, Comma, Sp,
                    F.Id("Z"), Dot, F.Id("conjugation"), Open, F.Id("n"), Close, Comma, Sp,
                    F.Id("Z"), Dot, F.Id("conjugation"), Open,
                    F.Id("Z"), Dot, F.Id("reflection"), Open, F.Id("n"), Close, Close,
                    CloseBrace, Sp, Eq, Sp, D(4), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Conditional on a supplied duplicate-free exhaustive ZeroData enumeration, "
                    + "an index with a distinct conjugation partner and an off-critical-line "
                    + "zero has exactly four indices in its reflection-conjugation orbit. The "
                    + "proof uses the public commutation, mirror fixed-point, and involution "
                    + "theorems to establish pairwise distinctness. It constructs no ZeroData "
                    + "inhabitant, asserts no off-line zero exists, and makes no Riemann "
                    + "hypothesis claim."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Zeros/Symmetry/ZeroSymmetryAction")),
        ]));
}
