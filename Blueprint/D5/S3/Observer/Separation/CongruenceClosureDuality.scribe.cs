using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Separation;

internal sealed class CongruenceClosureDualityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Forward congruences have dual repairs, common fixed points, and an adjoint triple.",
        H("Congruence Closure Duality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("dual-congruence-repairs-and-adjoint-triple"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Separation/CongruenceClosureDuality."
                        + "dual_congruence_repair_laws"),
                H("Dual canonical repairs of an equivalence relation"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Equivalence relations on Y are ordered by relation inclusion. "
                            + "The predictive interior reuses the all-iterate congruence "
                            + "kernel, while the forgetting closure is the least stable "
                            + "setoid above its input.")),
                    Paragraph(Text(
                        "The theorem proves contraction, monotonicity, and idempotence "
                            + "for the interior; extensivity, monotonicity, and idempotence "
                            + "for the closure; the common fixed-point characterization; "
                            + "both Galois connections; and the repair sandwich."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("Y");
        Formula update = F.Id("F");
        Formula relation = F.Id("R");
        Formula stable = Call("IsForwardCongruence", update, relation);
        Formula interior = Call("I", update, relation);
        Formula closure = Call("C", update, relation);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            update, Colon, Sp, state, Sp, To, Sp, state, Comma, RowBreak,
            Forall, Sp, relation, Colon, Sp, Call("Setoid", state), Comma, RowBreak,
            interior, Sp, Eq, Sp, relation, Sp, Iff, Sp, stable, Sp, Iff, Sp,
            closure, Sp, Eq, Sp, relation, Comma, RowBreak,
            interior, Sp, Subseteq, Sp, relation, Sp, Land, Sp,
            relation, Sp, Subseteq, Sp, closure, Comma, RowBreak,
            Call("GaloisConnection", F.Id("closureRepair"), F.Id("inclusion")), Sp,
            Land, Sp,
            Call("GaloisConnection", F.Id("inclusion"), F.Id("interiorRepair")), Dot,
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
