using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Completion;

internal sealed class CompletionPointCovarianceDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Completion/CompletionPointCovariance."
            + "completion_point_covariance";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Completion-point carriers are covariant under parameter equivalences that preserve "
            + "normalization and zero defect.",
        H("Completion Point Covariance"),
        Blocks(Describe.Lean(
            DescribeId.Create("completion-point-covariance"),
            DeclarationHandle.Create(Declaration),
            H("Preserving the defining predicates transports completion points"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The completion carrier is the repository's canonical constrained "
                        + "zero-defect subtype. A parameter equivalence preserving each of its "
                        + "two predicates therefore restricts to the displayed equivalence.")),
                Paragraph(Text(
                    "The Lean term is Mathlib's exact subtype equivalence construction. Its "
                        + "forward map sends a completion point with parameter a to the point "
                        + "whose parameter is alpha(a), and the inverse is inherited from alpha."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TheoremFormula()
    {
        Formula parameter = F.Id("A");
        Formula parameterPrime = F.Id("APrime");
        Formula defectType = F.Id("D");
        Formula defectTypePrime = F.Id("DPrime");
        Formula type = F.Id("Type");
        Formula normalization = F.Id("N");
        Formula normalizationPrime = F.Id("NPrime");
        Formula defect = Delta;
        Formula defectPrime = F.Id("DeltaPrime");
        Formula zeroD = F.Id("zeroD");
        Formula zeroDPrime = F.Id("zeroDPrime");
        Formula alpha = Alpha;
        Formula point = F.Id("a");
        Formula pointPrime = F.Id("aPrime");
        Formula alphaPoint = Apply(alpha, point);
        Formula completion = Seq(
            OpenBrace, Typed(point, parameter), Sp, Mid, Sp,
            point, InMacro, Sp, normalization, Sp, Land, Sp,
            Apply(defect, point), Sp, Eq, Sp, zeroD, CloseBrace);
        Formula completionPrime = Seq(
            OpenBrace, Typed(pointPrime, parameterPrime), Sp, Mid, Sp,
            pointPrime, InMacro, Sp, normalizationPrime, Sp, Land, Sp,
            Apply(defectPrime, pointPrime), Sp, Eq, Sp, zeroDPrime, CloseBrace);
        Formula normalizationClause = Seq(
            Forall, Sp, Typed(point, parameter), Comma, Sp,
            point, InMacro, Sp, normalization, Sp, Iff, Sp,
            alphaPoint, InMacro, Sp, normalizationPrime);
        Formula defectClause = Seq(
            Forall, Sp, Typed(point, parameter), Comma, Sp,
            Apply(defect, point), Sp, Eq, Sp, zeroD, Sp, Iff, Sp,
            Apply(defectPrime, alphaPoint), Sp, Eq, Sp, zeroDPrime);

        return Disp(Seq(
            Forall, Sp,
            Typed(parameter, type), Comma, Sp,
            Typed(parameterPrime, type), Comma, Sp,
            Typed(defectType, type), Comma, Sp,
            Typed(defectTypePrime, type), Comma, Sp,
            Typed(normalization, Call("Set", parameter)), Comma, Sp,
            Typed(normalizationPrime, Call("Set", parameterPrime)), Comma, RowBreak,
            Typed(defect, Seq(parameter, Sp, To, Sp, defectType)), Comma, Sp,
            Typed(defectPrime, Seq(parameterPrime, Sp, To, Sp, defectTypePrime)), Comma, Sp,
            Typed(zeroD, defectType), Comma, Sp,
            Typed(zeroDPrime, defectTypePrime), Comma, Sp,
            Typed(alpha, Call("Equiv", parameter, parameterPrime)), Comma, RowBreak,
            Open, normalizationClause, Close, Sp, Land, Sp,
            Open, defectClause, Close, Sp, Rightarrow, RowBreak,
            Call("Bijective", Seq(
                alpha, Colon, Sp, completion, Sp, To, Sp, completionPrime)), Dot));
    }
}
