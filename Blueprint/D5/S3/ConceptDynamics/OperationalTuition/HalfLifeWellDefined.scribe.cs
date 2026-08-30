using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.OperationalTuition;

internal sealed class HalfLifeWellDefinedDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/OperationalTuition/HalfLifeWellDefined."
            + "half_life_computable_and_ink_not_dry_nontrivial";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite same-class capture histories have an executable least stable gate suffix, "
            + "while the ink-not-dry recurrence remains unconverged.",
        H("Finite Error-Class Half-Life"),
        Blocks(Describe.Lean(
            DescribeId.Create("half-life-computable-with-ink-not-dry-witness"),
            DeclarationHandle.Create(Declaration),
            H("Half-life is computable and the ink-not-dry trace is nontrivial"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The frozen operational trajectory supplies a finite event list and its "
                        + "same-class capture history. The executable half-life searches the "
                        + "finite list of suffixes and rejects the empty suffix.")),
                Paragraph(Text(
                    "A returned index is characterized independently: its nonempty suffix is "
                        + "entirely gate-or-higher, and every earlier suffix fails that condition. "
                        + "Thus the value is the first stable capture index, not merely any "
                        + "successful suffix.")),
                Paragraph(Text(
                    "The ink-not-dry witness contains three occurrences of one error class, all "
                        + "captured at wall level. Its compiled maturity list is exactly three "
                        + "walls and its executable half-life is none."))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/ConceptDynamics/OperationalTuition/"
                + "InstitutionalMappingAndCaptureFiltration"))]));

    private static Formula Typeclass(string name, Formula argument) =>
        Seq(OpenBracket, Call(name, argument), CloseBracket);

    private static Formula ListLiteral(params Formula[] items)
    {
        var content = new List<Formula> { OpenBracket };
        for (var index = 0; index < items.Length; index++)
        {
            if (index > 0) content.AddRange([Comma, Sp]);
            content.Add(items[index]);
        }
        content.Add(CloseBracket);
        return Seq([.. content]);
    }

    private static Formula TheoremFormula()
    {
        Formula errorClass = F.Id("C");
        Formula institution = F.Id("I");
        Formula trajectory = F.Id("tau");
        Formula error = F.Id("c");
        Formula index = F.Id("n");
        Formula earlier = F.Id("m");
        Formula maturity = Call("classMaturity", trajectory, error);
        Formula stableHere = Call("StableAtGate", maturity, index);
        Formula noEarlier = Seq(
            Forall, Sp, earlier, Colon, Sp, F.Id("Nat"), Comma, Sp,
            earlier, Sp, Lt, Sp, index, Sp, Rightarrow, Sp,
            Neg, Sp, Call("StableAtGate", maturity, earlier));
        Formula characterization = Seq(
            Call("gateHalfLife", trajectory, error), Sp, Eq, Sp,
            Call("some", index), Sp, Iff, Sp,
            Open, stableHere, Sp, Land, Sp, noEarlier, Close);
        Formula inkTrajectory = F.Id("inkNotDryTrajectory");
        Formula unit = F.Id("unit");
        Formula inkHistory = Seq(
            Call("classMaturity", inkTrajectory, unit), Sp, Eq, Sp,
            ListLiteral(F.Id("wall"), F.Id("wall"), F.Id("wall")));
        Formula inkUnconverged = Seq(
            Call("gateHalfLife", inkTrajectory, unit), Sp, Eq, Sp, F.Id("none"));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, errorClass, Comma, Sp, institution,
                Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma),
            Seq(Grp(), Typeclass("DecidableEq", errorClass), Comma),
            Seq(
                trajectory, Colon, Sp,
                Call("OperationalTrajectory", errorClass, institution), Comma),
            Seq(
                error, Colon, Sp, errorClass, Comma, Sp,
                index, Colon, Sp, F.Id("Nat"), Comma),
            Seq(Open, characterization, Close, Sp, Land),
            Seq(Grp(), Open, inkHistory, Close, Sp, Land),
            Seq(Grp(), inkUnconverged, Dot),
        ]));
    }
}
