using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer;

internal sealed class RiemannNamingStabilityReductionDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/RiemannNamingStabilityReduction."
            + "riemann_naming_stability_reduction";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The RH naming-stability claim reduces exactly to the missing shifted-response "
            + "congruence bridge.",
        H("Riemann Naming Stability Reduction"),
        Blocks(Describe.Lean(
            DescribeId.Create("riemann-naming-stability-reduction"),
            DeclarationHandle.Create(Declaration),
            H("Conditional interior-closure fixed-point equivalence"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The shifted response and reflection-name relation remain abstract. "
                        + "The hypothesis isolates the missing analytic theorem that RH "
                        + "is equivalent to forward congruence of that relation.")),
                Paragraph(Text(
                    "Under precisely that bridge, the existing dual repair theorem "
                        + "identifies RH with the interior fixed point, the closure fixed "
                        + "point, and their simultaneous fixed-point equation."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula rh = F.Id("RH");
        Formula update = F.Id("F_shift");
        Formula relation = F.Id("R_J");
        Formula stable = Call("IsForwardCongruence", update, relation);
        Formula interiorFixed = Seq(Call("I", update, relation), Sp, Eq, Sp, relation);
        Formula closureFixed = Seq(Call("C", update, relation), Sp, Eq, Sp, relation);
        Formula tripleFixed = Seq(
            Call("I", update, relation), Sp, Eq, Sp, relation, Sp, Eq, Sp,
            Call("C", update, relation));

        return Disp(Seq(
            Grp(rh, Sp, Iff, Sp, stable), Sp, To, Sp,
            Begin, Grp(F.Id("gathered")),
            Grp(rh, Sp, Iff, Sp, interiorFixed), Comma, RowBreak,
            Grp(rh, Sp, Iff, Sp, stable), Comma, RowBreak,
            Grp(rh, Sp, Iff, Sp, closureFixed), Comma, RowBreak,
            Grp(rh, Sp, Iff, Sp, tripleFixed), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }
}
