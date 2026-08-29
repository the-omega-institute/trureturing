using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InvolutionLogic;

internal sealed class SingletonRelativeComplementCriterionDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/InvolutionLogic/SingletonRelativeComplementCriterion."
        + "singleton_relative_complement_iff_two_point_universe";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A singleton relative complement exists exactly when the ambient set is the corresponding two-point set.",
        H("Singleton Relative Complement Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("singleton-relative-complement-iff-two-point-universe"),
                DeclarationHandle.Create(Declaration),
                H("A singleton relative complement characterizes a two-point ambient set"),
                StatementSource.FromAuthor(CriterionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix a point t in an ambient set Omega. If removing t leaves exactly "
                            + "one distinct point s, every ambient point is t or s.")),
                    Paragraph(Text(
                        "Conversely, if Omega consists of the distinct points t and s, "
                            + "removing t leaves exactly the singleton containing s."))),
                DescribeRole.Theorem))));

    private static Formula Singleton(Formula value) =>
        Seq(OpenBrace, value, CloseBrace);

    private static Formula CriterionFormula()
    {
        Formula carrier = F.Id("X");
        Formula ambient = F.Id("Omega");
        Formula point = F.Id("t");
        Formula witness = F.Id("s");
        Formula witnessConditions = Seq(
            witness, Sp, InMacro, Sp, ambient, Sp, Land, Sp,
            witness, Sp, Neq, Sp, point);
        Formula complementWitness = Seq(
            Exists, Sp, witness, Colon, Sp, carrier, Comma, Sp,
            witnessConditions, Sp, Land, Sp,
            ambient, Sp, Setminus, Sp, Singleton(point), Sp, Eq, Sp,
            Singleton(witness));
        Formula twoPointWitness = Seq(
            Exists, Sp, witness, Colon, Sp, carrier, Comma, Sp,
            witnessConditions, Sp, Land, Sp,
            ambient, Sp, Eq, Sp,
            Seq(OpenBrace, point, Comma, Sp, witness, CloseBrace));

        return Disp(Seq(
            Forall, Sp, carrier, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            ambient, Colon, Sp, Call("Set", carrier), Comma, Sp,
            point, Colon, Sp, carrier, Comma, Sp,
            point, Sp, InMacro, Sp, ambient, Sp, Rightarrow, Sp,
            Open, complementWitness, Close, Sp, Iff, Sp,
            Open, twoPointWitness, Close, Dot));
    }
}
