using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros;

internal sealed class UpperZeroReflectionNameInjectivityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "RH is equivalent to injectivity of the unordered reflection-orbit name on upper zeros.",
        H("Upper-Zero Reflection Name Injectivity"),
        Blocks(Describe.Lean(
            DescribeId.Create("rh-exactly-when-upper-reflection-names-are-injective"),
            DeclarationHandle.Create(
                "D5/S3/Zeros/UpperZeroReflectionNameInjectivity."
                    + "rh_iff_upper_zero_reflection_name_injective"),
            H("RH is injectivity of the upper reflection name"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For a supplied duplicate-free exhaustive ZeroData enumeration, the left "
                        + "side says that every classical nontrivial zero has critical real "
                        + "part. The right side says that the unordered conjugate-reflection "
                        + "orbit name is injective on indices whose zeros lie in the open upper "
                        + "half-plane.")),
                Paragraph(Text(
                    "Conjugate reflection is an involution preserving the upper half-plane. "
                        + "An index and its mirror always have the same unordered name, so "
                        + "injectivity forces every upper orbit to be a singleton. Conversely, "
                        + "singleton upper orbits reduce the name to an unordered repeated pair "
                        + "and hence make it injective.")),
                Paragraph(Text(
                    "The existing mirror fixed-point characterization converts singleton "
                        + "orbits into critical-line membership. Existing nonvanishing on the "
                        + "real interval and conjugation transport the upper-half-plane result "
                        + "to every nontrivial zero. The theorem constructs no ZeroData "
                        + "inhabitant and therefore does not assert RH unconditionally."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Weil/ZetaBridge/AlternatingZetaContinuation")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Zeros/Symmetry/ZeroSymmetryAction")),
        ]));

    private static Formula TheoremFormula()
    {
        Formula z = F.Id("Z");
        Formula rho = Rho;
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula isNontrivialZero = Seq(
            Operatorname, Grp(F.Id("IsNontrivialZero")), Open, rho, Close);
        Formula allZerosCritical = Seq(
            Forall, Sp, rho, InMacro, Sp, complex, Comma, Esc,
            isNontrivialZero, Sp, Rightarrow, Sp,
            Re, Open, rho, Close, Sp, Eq, Sp,
            Operatorname, Grp(F.Id("criticalAbscissa")));
        Formula reflectionName = Seq(
            Operatorname, Grp(F.Id("upperZeroReflectionName")), Open, z, Close);
        Formula injective = Seq(
            Operatorname, Grp(F.Id("Injective")), Open, reflectionName, Close);

        return Disp(Seq(
            Forall, Sp, z, Colon, Sp, Operatorname, Grp(F.Id("ZeroData")), Comma, Esc,
            Open, allZerosCritical, Close, Sp, Leftrightarrow, Sp, injective, Dot));
    }
}
