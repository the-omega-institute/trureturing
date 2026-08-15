using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics.EscapeProbability;

internal sealed class StrictAddressMonotonicityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed point makes frozen escape probability strictly increase with positive address count.",
        H("Strict Address Monotonicity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fixed-point-strict-address-monotonicity"),
                DeclarationHandle.Create(
                    "D5/S0/Asymptotics/EscapeProbability/StrictAddressMonotonicity."
                        + "escape_probability_strictMonoOn_of_has_fixed_point"),
                H("A fixed point gives strict monotonicity in positive address count"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("Y"), Comma, Sp,
                    OpenBracket, Operatorname, Grp(F.Id("Fintype")), Sp, F.Id("Y"),
                    CloseBracket, Sp,
                    OpenBracket, Operatorname, Grp(F.Id("Nonempty")), Sp, F.Id("Y"),
                    CloseBracket, Comma, Sp,
                    Forall, Sp, F.Id("f"), Colon, Sp, F.Id("Y"), Sp, To, Sp, F.Id("Y"),
                    Comma, Sp,
                    D(2), Sp, Leq, Sp, Call("card", F.Id("Y")), Sp, Rightarrow, Sp,
                    D(0), Sp, Lt, Sp, Call("card", Call("Fix", F.Id("f"))),
                    Sp, Rightarrow, Sp,
                    Call("StrictMonoOn",
                        Seq(Open, F.Id("A"), Sp, Mapsto, Sp,
                            Call("escapeProbability", Call("Fin", F.Id("A")), F.Id("f")),
                            Close),
                        Call("Ici", D(1))), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite nonempty output type Y with at least two elements, if f "
                            + "has at least one fixed point, then its frozen escape probability "
                            + "is strictly increasing as the positive address count grows.")),
                    Paragraph(Text(
                        "The proof applies the public frozen closed form at consecutive address "
                            + "counts. A strict auxiliary ratio comparison uses the positive "
                            + "fixed-point count, and pinned Mathlib's strictMonoOn_of_lt_succ "
                            + "promotes the successor inequality to strict monotonicity on Ici 1."))),
                DescribeRole.Theorem)),
        []));
}
