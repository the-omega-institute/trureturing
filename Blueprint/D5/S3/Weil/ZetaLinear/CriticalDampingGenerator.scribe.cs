using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaLinear;

internal sealed class CriticalDampingGeneratorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized diagonal zero generator is skew-adjoint exactly on the critical line.",
        H("Critical Damping Generator"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("normalized-generator-skew-adjoint-criterion"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/ZetaLinear/CriticalDampingGenerator."
                        + "normalized_generator_skew_iff_critical_line"),
                H("The normalized generator is skew-adjoint exactly on the critical line"),
                StatementSource.FromAuthor(Disp(Formula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The mode carrier is the sigma type of an enumerated zero index together "
                        + "with a multiplicity fiber Fin (Z.multiplicity n). At a mode v, the "
                        + "generator scalar is minus omega plus Re(Z.zero v.1) minus the "
                        + "critical abscissa, plus i times the ordinate, with the uniform omega "
                        + "shift added back. Pointwise conjugate-equals-negative is the "
                        + "skew-adjoint condition, and it is equivalent to the critical-line "
                        + "condition."))),
                DescribeRole.Theorem))));

    private static Formula Formula()
    {
        var z = F.Id("Z");
        var omega = F.Id("omega");
        var v = F.Id("v");
        var mode = Call("normalizedMode", omega,
            Seq(F.Id("Z"), Dot, F.Id("zero"), Open, Call("first", v), Close));
        var left = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("n"),
                Seq(Mathbb, Sp, Grp(F.Id("N"))))],
            Equal(Seq(Re, Open,
                Seq(F.Id("Z"), Dot, F.Id("zero"), Open, F.Id("n"), Close), Close),
                Call("criticalAbscissa")));
        var right = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("v"),
                Call("zeroModeIndex", z))],
            Equal(Call("conj", mode), Call("neg", mode)));
        var core = new Formula.Logic(left, FormulaLogicOperator.Iff, right);
        return Seq(
            Forall, Sp, z, Colon, Sp, Operatorname, Grp(F.Id("ZeroData")), Comma, Sp,
            Forall, Sp, omega, Colon, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            new Formula.Logic(
                new Formula.Relation(Seq(Frac, Grp(Num(1)), Grp(Num(2))),
                    FormulaRelationOperator.LessThanOrEqual, omega),
                FormulaLogicOperator.Implies,
                core));
    }
}
